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

case class Input() extends Bundle {
  // 0: first argument / result
  // 1: second argument / result overflow
  // 2: isProcessing (status)
  // 3: unused
  val addr = UInt (2 bits)

  // whether it's an MMIO read or write
  val isWrite = Bool()

  // is isWrite, the value to be written, else unused
  val valueIn = UInt (4 bits)
}

case class Output() extends Bundle {
  // if !isWrite, the result of the read
  val valueOut = UInt (4 bits)
}

case class MultiplierIO() extends Bundle {
  val input = in (Input())
  val output = out (Output())
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
  switch(io.input.addr) {
    is(0) { io.output.valueOut := a }
    is(1) { io.output.valueOut := b }
    default {
      when(state === StateType.READY) {
        io.output.valueOut := 0
      } otherwise {
        io.output.valueOut := 1
      }
    }
  }

  def summand(i: Int): UInt =
    U(8 bits, (i+3 downto i) -> Mux(b(i), a, U(0)), default -> false)

  switch(state) {
    is(StateType.READY) {
      when(io.input.isWrite) {
        switch(io.input.addr) {
          is(0) { a := io.input.valueIn }
          is(1) { b := io.input.valueIn }
          is(2) { when(io.input.valueIn === 1) { state := StateType.PROCESSING0 } }
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
      adder.io.x := summand(0)
      adder.io.y := summand(1)
      r := adder.io.r
      state := StateType.PROCESSING1
    }
    is(StateType.PROCESSING1) {
      adder.io.x := r
      adder.io.y := summand(2)
      r := adder.io.r
      state := StateType.PROCESSING2
    }
    is(StateType.PROCESSING2) {
      adder.io.x := r
      adder.io.y := summand(3)
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

object Spec {
  def validAddr(a: UInt): Bool = a === U(0) || a === U(1) || a === U(2)

  def acceptsInput(s: SpecStateData, input: Input): Bool =
    s.state.mux(
      SpecState.READY ->
        (Mux(input.isWrite, validAddr(input.addr), True) &&
         Mux(input.isWrite && input.addr === U(2), input.valueIn === U(1), True)),
      SpecState.PROCESSING -> (input.isWrite === False)
    )

  def isAcceptableDelay(n: UInt): Bool =
    n === U(0) || n === U(1) || n === U(2) || n === U(3) || n === U(4)

  // Only consulted if acceptsInput(s1, input) returns True.
  // Can allow many different outputs and next states s2, and the implementation can choose any of them.
  def step(s1: SpecStateData, input: Input, output: Output, s2: SpecStateData): Bool =
    s1.state.mux(
      SpecState.READY ->
        input.isWrite.mux(
          // it's a write
          True -> input.addr.mux(
            0 -> (s2.state === SpecState.READY && s2.a === input.valueIn && s2.b === s1.b),
            1 -> (s2.state === SpecState.READY && s2.b === input.valueIn && s2.a === s1.a),
            2 -> (s2.state === SpecState.PROCESSING && s2.a === s1.a && s2.b === s1.a && isAcceptableDelay(s2.n)),
            default -> False
          ),
          // it's a read
          False -> (s2 === s1 && input.addr.mux(
            0 -> (output.valueOut === s1.a),
            1 -> (output.valueOut === s1.b),
            2 -> (output.valueOut === U(0)),
            default -> False
          ))
        ),
      SpecState.PROCESSING -> (
        input.isWrite === False &&
        Mux(input.addr === U(2), output.valueOut === U(1), True) &&
        s1.n.mux(
          0 -> (s2.state === SpecState.READY && s2.a === (s1.a * s1.b)(3 downto 0) && s2.b === (s1.a * s1.b)(7 downto 4)),
          default -> (s2.state === SpecState.PROCESSING && s2.a === s1.a && s2.b === s1.b && s2.n === s1.n - 1)
        )
      )
    )
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

  // TODO maybe we can use k-induction to define a generic invariant that says
  // "going k steps backwards from s is possible or hits an initial state"
  def implStateValid(s: MultiplierImpl): Bool =
    s.state.mux(
      StateType.READY -> True, // TODO will need to distinguish if we're holding a result or not
      StateType.PROCESSING0 -> (s.r === s.summand(0) + s.summand(1)),
      StateType.PROCESSING1 -> (s.r === s.summand(0) + s.summand(1) + s.summand(2)),
      StateType.PROCESSING2 -> (s.r === s.summand(0) + s.summand(1) + s.summand(2) + s.summand(3))
    )
}

object MultiplierVerilog extends App {
  Config.spinal.generateVerilog(MultiplierImpl())
  Config.spinal.generateVerilog(Adder())
}

case class MultiplierFormalBench() extends Component {
  val io = new Bundle {
    val specState = in (SpecStateData())
  }

  val impl = MultiplierImpl()
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
      // assumeInitial(clockDomain.isResetActive)
      assumeInitial(ProofHelpers.f(dut.impl) === dut.io.specState)
      assumeInitial(ProofHelpers.implStateValid(dut.impl))
      assumeInitial(Spec.acceptsInput(dut.io.specState, dut.impl.io.input))

      assert(Spec.step(past(dut.io.specState), past(dut.impl.io.input), past(dut.impl.io.output), dut.io.specState))
    })
}
