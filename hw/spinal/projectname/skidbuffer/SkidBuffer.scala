package projectname.skidbuffer

import spinal.core._
import scala.language.postfixOps

/*
## Purely functional spec of unbounded queue in Coq:

Definition queue(T: Type) := list T.

Definition empty_queue{T: Type}: queue T := [].

Definition enqueue{T: Type}(q: queue T)(x: T): queue T := q ++ [x].

Definition dequeue{T: Type}(q: queue T): queue T :=
  match q with
  | h :: t => t
  | [] => []
  end.

Definition front{T: Type}`{inhabited T}(q: queue T): T :=
  match q with
  | h :: t => h
  | [] => default
  end.


## Skid buffer spec in a fictional, imperative embedded DSL in Coq

Definition skid_buffer(T: type) := FSM {
  const CAPACITY := 2;
  var q: queue<T> := empty_queue;

  (* upstream: *)
  input uValid: Bool;
  output uReady: Bool;
  input uData: T;

  (* downstream: *)
  output dValid: Bool;
  input dReady: Bool;
  output dData: T;

  (* Only one single state. In each cycle, the following procedure runs: *)
  entry state the_only_state {
    dValid := (length(q) > 0);
    uReady := (length(q) < CAPACITY);
    if (dValid) {
      dData := front(q);
      if (dReady) {
        q := dequeue(q);
      }
    };
    if (uReady && uValid) {
      q := enqueue(q, uData);
    }
  }
}


## Refined skid buffer in the same language, but with a finite queue

It seems that SymbiYosys does not support data structures of unbounded size,
so we rewrite the spec to use a circular buffer instead of an unbounded queue,
and we'll prove in Coq that the spec with the circular buffer refines the spec
with the unbounded queue.

Definition skid_buffer_bounded(T: type) := FSM {
  var buf: Vec(T, 2);
  var sz: UInt(2) = 0;
  var enqPtr: UInt(1) = 0;
  var deqPtr: UInt(1) = 0;

  (* upstream: *)
  input uValid: Bool;
  output uReady: Bool;
  input uData: T;

  (* downstream: *)
  output dValid: Bool;
  input dReady: Bool;
  output dData: T;

  (* Only one single state. In each cycle, the following procedure runs: *)
  entry state the_only_state {
    dValid := (sz > 0);
    uReady := (sz < 2);
    if (dValid) {
      dData := buf[deqPtr];
      if (dReady) {
        deqPtr := deqPtr + 1;
        sz := sz - 1
      }
    };
    if (uReady && uValid) {
      buf[enqPtr] := uData;
      enqPtr := enqPtr + 1;
      sz := sz + 1
    }
  }
}

Note: The addition on deqPtr and enqPtr wraps around, i.e. it is modulo 2.


## Translating the spec to SpinalHDL -- Data types */

// TODO is this the proper way to define generic bundles? (call-by-name args aren't supported as case class arguments)
case class SpecStateData[T <: Data](dataType: () => T) extends Bundle {
  val buf = Vec(dataType(), 2)
  val sz = UInt (2 bits)
  val enqPtr = UInt (1 bits)
  val deqPtr = UInt (1 bits)
}

case class Input[T <: Data](dataType: () => T) extends Bundle {
  val dReady = Bool()
  val uValid = Bool()
  val uData = dataType()
}

case class Output[T <: Data](dataType: () => T) extends Bundle {
  val uReady = Bool()
  val dValid = Bool()
  val dData = dataType()
}

object Lib {
  // TODO doesn't SpinalHDL already support this?
  def updateNth[T <: Data](v: Vec[T], n: UInt, x: T): Vec[T] = {
    // If only SpinalHDL was more functional-programming-minded...
    // Here I have to make an explicit copy using the non-obviously-named CombInit constructor,
    // and then assign to that copy
    val res: Vec[T] = CombInit(v)
    res(n) := x
    res
  }

  def implies(a: Bool, b: Bool): Bool = (!a) || b
}
import Lib._

/*
## Translating the spec to SpinalHDL -- Step function

A variable mapping V is a dictionary that maps variable names to values.
We sketch denotational semantics of the imperative language that translate
imperative programs to pure functions from variable mappings to variable mappings:

interpCmd (c1; c2) := (fun V => let V' := interpCmd c1 V in interpCmd c2 V')
interpCmd (x := e) := (fun V => V[x := interpExpr e V])
interpCmd (x[e1] := e2) := (fun V => V[x := V[x][(interpExpr e1 V) := (interpExpr e2 V)]])
interpCmd (if e {c1} else {c2}) := (fun V => if interpExpr e V then interpCmd c1 V else interpCmd c2 V)
interpCmd ({}) := (fun V => V)

Note that "if e {c1}" is a shorthand for "if e {c1} else {}".
Also note that we omit the definition of interpExpr,
and we are a bit sloppy about what's deeply vs shallowly embedded.
And probably interpExpr should be a partial function that fails if e.g. an non-existent variable is looked up.

Now, let's apply interpCmd to the procedure of the_only_state:

fun V =>                                                    (* Imperative program:       *)
  let V' := V[dValid := V[sz] > 0] in                       (* dValid := (sz > 0);       *)
  let V'' := V'[uReady := V'[sz] < 2] in                    (* uReady := (sz < 2);       *)
  let VM := if V''[dValid] then                             (* if (dValid) {             *)
    let V''' := V''[dData := V''[buf][deqPtr]] in           (*   dData := buf[deqPtr];   *)
    if V'''[dReady] then                                    (*   if (dReady) {           *)
      let V'''' := V'''[deqPtr := V'''[deqPtr] + 1] in      (*     deqPtr := deqPtr + 1; *)
      V''''[sz := V'''[sz] - 1]                             (*     sz := sz - 1          *)
    else V'''                                               (*   }                       *)
  else V'' in                                               (* };                        *)
  if VM[uReady] && VM[uValid] then                          (* if (uReady && uValid) {   *)
    let VM' := VM[buf := VM[buf][enqPtr := VM[uData]]] in   (*   buf[enqPtr] := uData;   *)
    let VM'' := VM'[enqPtr := VM'[enqPtr] + 1] in           (*   enqPtr := enqPtr + 1;   *)
    VM''[sz := VM''[sz] + 1]                                (*   sz := sz + 1            *)
  else VM                                                   (* }                         *)

Now, let's apply this function to a variable mapping that contains references to
all state variables and all input variables, but no output variables yet:

V := [buf := current.buf,
      sz := current.sz,
      enqPtr := current.enqPtr,
      deqPtr := current.deqPtr,
      uValid := input.uValid,
      uData := input.uData,
      dReady := input.dReady]

If we inline all the map getters and some let binders, we obtain the following
final variable mapping:

let VF :=
  let VM := if (current.sz > 0) then
    if (current.sz < 2) then
      V[dValid := (current.sz > 0),
        uReady := (current.sz < 2),
        dData := current.buf[current.deqPtr],
        deqPtr := current.deqPtr + 1,
        sz := current.sz - 1]
    else
      V[dValid := (current.sz > 0),
        uReady := (current.sz < 2),
        dData := current.buf[current.deqPtr]]
  else V[dValid := (current.sz > 0),
         uReady := (current.sz < 2)]
  in
  if current.sz < 2 && input.uValid then
    VM[buf := current.buf[current.enqPtr := input.uData],
       enqPtr := current.enqPtr + 1,
       sz := current.sz + 1]
  else VM

Now, if we had a synthesizable form of VF, we could define the spec step function in SpinalHDL as follows:

def step(current: State, input: Input, output: Output, next: State): Bool =
  (if VF.has(uReady) { output.uReady == VF[uReady] } else { true }) &&
  (if VF.has(dValid) { output.dValid == VF[dValid] } else { true }) &&
  (if VF.has(dData)  { output.dData  == VF[dData]  } else { true }) &&
  (if VF.has(buf)    { next.buf      == VF[buf]    } else { next.buf == current.buf }) &&
  (if VF.has(sz)     { next.sz       == VF[sz]     } else { next.sz == current.sz }) &&
  (if VF.has(enqPtr) { next.enqPtr   == VF[enqPtr] } else { next.enqPtr == current.enqPtr }) &&
  (if VF.has(deqPtr) { next.deqPtr   == VF[deqPtr] } else { next.deqPtr == current.deqPtr })

Note that not assigning an output means it can be anything, whereas not assigning a state variable means it
remains the same as in the current state.

But unfortunately, dictionaries from variable names to values are not synthesizable, and also cannot be
partially evaluated away during SpinalHDL elaboration, because in accesses like VM[buf], where VM is defined
as (if exprOnlyKnownAtRuntime then ... else ...), the _[buf] access needs to be pushed down into both branches,
and SpinalHDL (probably?) can't do that.
But it seems possible to do this kind of partial evaluation semi-automatically in Coq.
After such partial evaluation, we might obtain the following step function: */

object Spec {

  def step[T<:Data](current: SpecStateData[T], input: Input[T], output: Output[T], next: SpecStateData[T]): Bool =
    // output:
    (output.uReady === (current.sz < 2)) &&
    (output.dValid === (current.sz > 0)) &&
    Mux(current.sz > 0,
      output.dData === current.buf(current.deqPtr),
      True) &&
    // next state:
    Mux(current.sz < 2 && input.uValid,
      next.buf === updateNth(current.buf, current.enqPtr, input.uData),
      next.buf === current.buf) &&
    Mux(current.sz > 0 && input.dReady,
      Mux(current.sz < 2 && input.uValid,
        next.sz === current.sz - 1 + 1,
        next.sz === current.sz - 1),
      Mux(current.sz < 2 && input.uValid,
        next.sz === current.sz + 1,
        next.sz === current.sz)) &&
    Mux(current.sz < 2 && input.uValid,
      next.enqPtr === current.enqPtr + 1,
      next.enqPtr === current.enqPtr) &&
    Mux(current.sz > 0 && input.dReady,
      next.deqPtr === current.deqPtr + 1,
      next.deqPtr === current.deqPtr)

  def initialSpecState[T <: Data](dataType: () => T): SpecStateData[T] = {
    val init = SpecStateData(dataType)
    init.buf := Vec.fill(2)(dataType())
    init.sz := 0
    init.enqPtr := 0
    init.deqPtr := 0
    init
  }
}

case class IO[T <: Data](dataType: () => T) extends Bundle {
  val input = in (Input(dataType))
  val output = out (Output(dataType))
}

// ## Implementation
// Loosely following https://fpgacpu.ca/fpga/Pipeline_Skid_Buffer.html, but without support for circular buffer mode

object SkidBufferFsmState extends SpinalEnum {
  // no elements in-flight
  val EMPTY = newElement()

  // normal operation, one element in-flight
  val BUSY = newElement()

  // downstream stalled, and to stop upstream, we had to store one extra element into the dataBufferReg,
  // so now two elements are in-flight
  val FULL = newElement()
}
import SkidBufferFsmState._

case class SkidBuffer[T <: Data](dataType: () => T) extends Component {
  val io = IO(dataType)
  val state = Reg(SkidBufferFsmState()) init EMPTY

  // The main register, always wired directly to the output (instead of connecting the output to a mux)
  // so that synthesis tools can more easily re-time it
  val dataOutputReg = Reg(dataType())

  // Extra register to make sure we don't lose an element when we skid as we stop the upstream
  val dataBufferReg = Reg(dataType())

  io.output.dData := dataOutputReg
  io.output.dValid := state =/= EMPTY
  io.output.uReady := state =/= FULL

  dataOutputReg := Mux(state === FULL && io.input.dReady, dataBufferReg, io.input.uData)
  dataBufferReg := io.input.uData

  switch(state) {
    is(EMPTY) {
      when(io.input.uValid) {
        state := BUSY
      }
    }
    is(BUSY) {
      when(io.input.uValid) {
        when(!io.input.dReady) {
          state := FULL
        }
      } otherwise {
        state := EMPTY
      }
    }
    is(FULL) {
      when(io.input.dReady) {
        state := BUSY
      }
    }
  }
}

// ## Proof

// Workaround needed because SpinalHDL does not allow me to write `past(s)` where `s` is a `Component`
case class ImplStateData[T <: Data](dataType: () => T) extends Bundle {
  val state = SkidBufferFsmState()
  val dataOutputReg = dataType()
  val dataBufferReg = dataType()
}

object ProofHelpers {
  // abstraction function
  // TODO can I do this without the extra dataType argument?
  def f[T <: Data](dataType: () => T)(s: ImplStateData[T]): SpecStateData[T] = {
    // TODO is there a functional way of doing this?
    val res = SpecStateData(dataType)
    // cannot find res.enqPtr/res.deqPtr!!
    res
  }

  // Note: We can't define an abstraction function from ImplStateData to SpecStateData
  // because each spec state has an equivalent spec state where buf, enqPtr and deqPtr
  // all are rotated by 1, and we don't know which of the two to pick if we can only
  // look at the current implementation state.
  // We might fix it by giving the abstraction function access to the previous spec state,
  // but that would result in a somewhat weird construct. It seems cleaner to use an
  // abstraction relation, and to add an explicit existential-finder function for the
  // new spec state that can depend on everything.

  def R[T <: Data](spec: SpecStateData[T], impl: ImplStateData[T]): Bool =
    spec.deqPtr + spec.sz(1 downto 0) === spec.enqPtr &&
    impl.state.mux(
      EMPTY -> True,
      BUSY -> (spec.enqPtr =/= spec.deqPtr &&
               spec.buf(spec.deqPtr) === impl.dataOutputReg),
      FULL -> (spec.enqPtr === spec.deqPtr &&
               spec.buf(spec.deqPtr) === impl.dataOutputReg &&
               spec.buf(spec.deqPtr + 1) === impl.dataBufferReg))

  // This function computes the existential for the statement
  // "exists next spec state such that spec steps to it and it's still related to impl state".
  // Not particularly interesting because this device is fully deterministic,
  // so the new spec state only depends on the old spec state and the input,
  // but more generally, it could also depend on the impl state and on the output
  def findNextSpecState[T <: Data](dataType: () => T)
    (spec: SpecStateData[T], impl: ImplStateData[T], input: Input[T], output: Output[T]): SpecStateData[T] =
  {
    val res = SpecStateData(dataType)
    // TODO implement this, which should make inductive step go through
    res
  }
}

case class SkidBufferFormalBench[T <: Data](dataType: () => T) extends Component {
  val impl = SkidBuffer(dataType)

  val implState = out (ImplStateData(dataType))
  // using .pull to work around hierarchy constraint that allows reading signals of
  // a child component only if they are marked as out
  implState.state := impl.state.pull()
  implState.dataOutputReg := impl.dataOutputReg.pull()
  implState.dataBufferReg := impl.dataBufferReg.pull()

  val implInput = in (Input(dataType))
  impl.io.input := implInput

  val implOutput = out (Output(dataType))
  implOutput := impl.io.output

  // to emulate a forall
  val arbitrarySpecState = in (SpecStateData(dataType))
}

import spinal.core.formal._
import ProofHelpers._
import Spec._

object Proof {
  def baseCase[T <: Data](dataType: () => T): Unit = {
    FormalConfig
      .withProve()
      .doVerify(new Component {
        val dut = FormalDut(SkidBufferFormalBench(dataType))

        assumeInitial(clockDomain.isResetActive)

        anyseq(dut.implInput)
        anyseq(dut.arbitrarySpecState) // not needed in base case, but all inputs need to be wired

        ClockDomain.current.duringReset {
          assert(R(initialSpecState(dataType), dut.implState))
        }
      })
  }

  def inductiveStep[T <: Data](dataType: () => T): Unit = {
    FormalConfig
      .withProve()
      .doVerify(new Component {
        val dut = FormalDut(SkidBufferFormalBench(dataType))

        anyseq(dut.implInput)
        anyseq(dut.arbitrarySpecState)

        // Note: Here we do NOT assume that there's a reset at the beginning!

        // don't run these in the first cycle, where no past(...) is available yet
        when(pastValid()) {
          // we can't use separate assume and assert statements instead of an implication,
          // because the separate assume statements would apply to each cycle, including the
          // second cycle, in which we want to assert stuff
          assert(implies(
            // If in the previous cycle, R held between an arbitrary spec state and the impl state, ...
            R(past(dut.arbitrarySpecState), past(dut.implState)),
            {
              val newSpecState = findNextSpecState(dataType)(
                past(dut.arbitrarySpecState), past(dut.implState), past(dut.implInput), past(dut.implOutput))
              // ... then we stepped to a new impl state and produced output that the spec allows ...
              step(past(dut.arbitrarySpecState), past(dut.implInput), past(dut.implOutput), newSpecState) &&
              // ... and R still holds
              R(newSpecState, dut.implState)
            }
          ))
        }
      })
  }
}

object SkidBufferFormalBaseCase extends App {
  // TODO does SpinalHDL testing/formal support some kind of opaque type,
  // so that we could prove correctness for all possible types at once?
  Proof.baseCase(() => UInt(32 bits))
}

object SkidBufferFormalInductiveStep extends App {
  Proof.inductiveStep(() => UInt(32 bits))
}
