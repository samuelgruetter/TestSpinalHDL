package projectname

import spinal.core._
import spinal.core.sim.SimDataPimper

import scala.language.postfixOps

object StateType extends SpinalEnum {
  val READY, PROCESSING0, PROCESSING1, PROCESSING2 = newElement()
}

case class MultiplierSpec() extends Component {
  val io = new Bundle {
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

  val state = Reg(StateType) init StateType.READY
  val a = Reg(UInt (4 bits))
  val b = Reg(UInt (4 bits))

  // we always drive io.valueOut -- TODO for the spec, could we leave it unspecified?
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
    }
    is(StateType.PROCESSING0) {
      state := StateType.PROCESSING1
    }
    is(StateType.PROCESSING1) {
      state := StateType.PROCESSING2
    }
    is(StateType.PROCESSING2) {
      val r = a * b
      a := r(3 downto 0)
      b := r(7 downto 4)
      state := StateType.READY
    }
  }
}

case class MultiplierImpl() extends Component {
  // same I/O as spec -- TODO what's a Bundle and can we share it?
  val io = new Bundle {
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
      b := adder.io.r(7 downto 4)
      // deliberate bug: drop highest bit of result
      // b := U(4 bits, 3 -> false, (2 downto 0) -> adder.io.r(6 downto 4))
      // TODO understand output of `yosys-witness display ./simWorkspace/unamed/unamed_bmc/engine_0/trace.yw`

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

import spinal.core.sim._

object MultiplierImplSim extends App {
  val maxAllowedLatency = 10

  //val compiled = Config.sim.compile(MultiplierImpl()) -- TODO why error if we reuse the compilation result?

  def simWithInput(arg1: Int, arg2: Int) = Config.sim.compile(MultiplierImpl()).doSim { dut => // device under test
    println(s"args: ${arg1} ${arg2}")

    // Fork a process to generate the reset and the clock on the dut
    dut.clockDomain.forkStimulus(period = 10)

    dut.clockDomain.waitRisingEdge()
    dut.io.addr #= 0
    dut.io.isWrite #= true
    dut.io.valueIn #= arg1

    dut.clockDomain.waitRisingEdge()
    dut.io.addr #= 1
    dut.io.isWrite #= true
    dut.io.valueIn #= arg2

    dut.clockDomain.waitRisingEdge()
    dut.io.addr #= 2
    dut.io.isWrite #= true
    dut.io.valueIn #= 1 // start processing

    var done = false
    var count = 0

    while (count < maxAllowedLatency && !done) {
      dut.clockDomain.waitRisingEdge()
      dut.io.addr #= 2
      dut.io.isWrite #= false
      // we're testing a Mealy machine (ie output depends on current inputs),
      // so give it half a cycle of time to propagate -- TODO is this kosher?
      dut.clockDomain.waitFallingEdge()
      val isProcessing = dut.io.valueOut.toInt
      println(s"count: ${count}, isProcessing: ${isProcessing}")
      println(s"r = ${dut.r.toInt}")
      if (isProcessing == 0) {
        done = true
      }
      count += 1
    }

    assert(done)

    dut.clockDomain.waitRisingEdge()
    dut.io.addr #= 0
    dut.io.isWrite #= false
    dut.clockDomain.waitFallingEdge()
    val loBits = dut.io.valueOut.toInt

    dut.clockDomain.waitRisingEdge()
    dut.io.addr #= 1
    dut.io.isWrite #= false
    dut.clockDomain.waitFallingEdge()
    val hiBits = dut.io.valueOut.toInt

    println(loBits)
    println(hiBits)
    assert(loBits + (hiBits << 4) == arg1 * arg2)
  }

  simWithInput(6, 7)
  simWithInput(3, 5)
  simWithInput(0, 6)
  simWithInput(6, 0)
  simWithInput(1, 1)
  simWithInput(4, 3)
  simWithInput(15, 15)
}

object MultiplierVerilog extends App {
  Config.spinal.generateVerilog(MultiplierSpec())
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

  val spec = MultiplierSpec()
  val impl = MultiplierImpl()
  (spec.io.addr, spec.io.isWrite, spec.io.valueIn) := (io.addr, io.isWrite, io.valueIn)
  (impl.io.addr, impl.io.isWrite, impl.io.valueIn) := (io.addr, io.isWrite, io.valueIn)
  io.comparisonOk := (io.isWrite || (spec.io.valueOut === impl.io.valueOut))
}

import spinal.core.formal._

object MultiplierFormalRunner extends App {
  FormalConfig
    //.withProve() // causes yices to run forever (at least >1min)
    //.withBMC(100) // runs forever
    //.withBMC(20) // 20 cycles takes a few minutes
    .withBMC(12) // succeeds quickly
    .doVerify(new Component {
      val dut = FormalDut(MultiplierFormalBench())

      // Ensure the formal test start with a reset
      // TODO where does this global variable clockDomain come from?
      assumeInitial(clockDomain.isResetActive)

      // Provide some stimulus
      anyseq(dut.io.addr)
      anyseq(dut.io.isWrite)
      anyseq(dut.io.valueIn)

      // to avoid disagreeing outputs before computation has taken place
      // TODO how can we specify the valid stimuli from the external world? (eg exclude reads as long as uninitialized)
      assumeInitial(dut.spec.a === dut.impl.a)
      assumeInitial(dut.spec.b === dut.impl.b)

      // Check the state initial value and increment
      assert(dut.io.comparisonOk)
    })
}
