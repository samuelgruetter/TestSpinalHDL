package projectname

import spinal.core._
import spinal.core.sim.SimDataPimper
import spinal.lib.fsm._

import scala.language.postfixOps

object StateType extends SpinalEnum {
  val READY, PROCESSING0, PROCESSING1, PROCESSING2 = newElement()
}

object SpecState extends SpinalEnum {
  val READY, PROCESSING = newElement()
}

case class SpecStateData() extends Bundle {
  val state = SpecState()
  val a = UInt (4 bits)
  val b = UInt (4 bits)
  val n = UInt (3 bits) // how many more processing steps are needed until we're done

  // These can't be inferred by an abstraction function that only looks at the implementation state!
  // TODO wrap implementation in another module that adds ghost state
  // val has_a = Bool() // whether a value for a has been written
  // val has_b = Bool() // whether a value for b has been written
}

case class MultiplierIO() extends Bundle {
  // 0: first argument / result
  // 1: second argument / result overflow
  // 2: isProcessing (status)
  // 3: unused
  val addr = in UInt (2 bits)

  // whether it's an MMIO read or write
  val isWrite = in Bool()

  // is isWrite, the value to be written, else unused
  val valueIn = in UInt (4 bits)

  // if !isWrite, the result of the read
  val valueOut = out UInt (4 bits)
}

case class MultiplierImpl() extends Component {
  val io = MultiplierIO()

  val state = Reg(StateType) init StateType.READY
  val a = Reg(UInt (4 bits))
  val b = Reg(UInt (4 bits))
  val r = Reg(UInt (8 bits))
  val adder = Adder()

  r.simPublic() // for debugging

  // we always drive io.valueOut
  switch(io.addr) {
    is(0) { io.valueOut := a }
    is(1) { io.valueOut := b }
    default {
      when(state === StateType.READY) {
        io.valueOut := 0
      } otherwise {
        io.valueOut := 1
      }
    }
  }

  switch(state) {
    is(StateType.READY) {
      when(io.isWrite) {
        switch(io.addr) {
          is(0) { a := io.valueIn }
          is(1) { b := io.valueIn }
          is(2) { when(io.valueIn === 1) { state := StateType.PROCESSING0 } }
        }
      }
      // We don't use the adder in this state but still need to assign its inputs to avoid creating latches
      adder.io.x := 0
      adder.io.y := 0
    }
    // We stage the computation b0*a + b1*(a<<1) + b2*(a<<2) + b3*(a<<3)
    // so that each cycle does one addition, so only one adder is needed,
    // and  the multiplications are just Muxes because their left argument is 1 bit only
    is(StateType.PROCESSING0) {
      adder.io.x := U(8 bits, (3 downto 0) -> Mux(b(0), a, U(0)), default -> false)
      adder.io.y := U(8 bits, (4 downto 1) -> Mux(b(1), a, U(0)), default -> false)
      r := adder.io.r
      state := StateType.PROCESSING1
    }
    is(StateType.PROCESSING1) {
      adder.io.x := r
      adder.io.y := U(8 bits, (5 downto 2) -> Mux(b(2), a, U(0)), default -> false)
      r := adder.io.r
      state := StateType.PROCESSING2
    }
    is(StateType.PROCESSING2) {
      adder.io.x := r
      adder.io.y := U(8 bits, (6 downto 3) -> Mux(b(3), a, U(0)), default -> false)
      r := adder.io.r
      a := adder.io.r(3 downto 0)

      // correct:
      // b := adder.io.r(7 downto 4)
      // deliberate bug: drop highest bit of result
      b := (U"1'b0" ## adder.io.r(6 downto 4)).asUInt
      // counterexamples are best viewed using
      // gtkwave ./simWorkspace/unamed/unamed_bmc/engine_0/trace.vcd &

      state := StateType.READY
    }
  }
}

case class Adder() extends Component {
  val io = new Bundle {
    val x = in UInt(8 bits)
    val y = in UInt(8 bits)
    val r = out UInt(8 bits)
  }
  io.r := io.x + io.y
}

object ProofHelpers {

  // abstraction function
  def f(s: MultiplierImpl): SpecStateData = {
    // TODO is there a functional way of doing this?
    val res = SpecStateData()
    res.state := (s.state match {
      case StateType.READY => SpecState.READY
      case _ => SpecState.PROCESSING
    })
    res.a := s.a
    res.b := s.b
    res.n := (s.state match {
      case StateType.PROCESSING0 => 3
      case StateType.PROCESSING1 => 2
      case StateType.PROCESSING2 => 1
      case _ => 0
    })
    res
  }

  def implStateValid(s: MultiplierImpl): Bool = {
    True
  }
}

object MultiplierVerilog extends App {
  Config.spinal.generateVerilog(MultiplierImpl())
  Config.spinal.generateVerilog(Adder())
}

case class MultiplierFormalBench() extends Component {
  val io = new Bundle {
    val addr = in UInt (2 bits)
    val isWrite = in Bool()
    val valueIn = in UInt (4 bits)
    val comparisonOk = out Bool()
  }

  /*
  val spec = MultiplierSpec()
  val impl = MultiplierImpl()

  spec.io.assignSomeByName(io)
  impl.io.assignSomeByName(io)

  io.comparisonOk := (io.isWrite || (spec.io.valueOut === impl.io.valueOut))
   */
}

import spinal.core.formal._

object MultiplierFormalStepRunner extends App {

  FormalConfig
    //.withProve() // causes yices to run forever (at least >1min)
    //.withBMC(100) // runs forever
    //.withBMC(20) // 20 cycles takes a few minutes
    .withBMC(12) // succeeds quickly
    .doVerify(new Component {
      val dut = FormalDut(MultiplierFormalBench())

      // Ensure the formal test start with a reset
      assumeInitial(clockDomain.isResetActive)
      // assumeInitial(R(dut.spec, dut.impl))

      // Provide some stimulus
      anyseq(dut.io.addr)
      anyseq(dut.io.isWrite)
      anyseq(dut.io.valueIn)

      // to avoid disagreeing outputs before computation has taken place
      // TODO how can we specify the valid stimuli from the external world? (eg exclude reads as long as uninitialized)
      // assumeInitial(dut.spec.a === dut.impl.a)
      // assumeInitial(dut.spec.b === dut.impl.b)

      // Check the state initial value and increment
      assert(dut.io.comparisonOk)
    })
}
