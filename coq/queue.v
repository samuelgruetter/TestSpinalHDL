Class inhabited(A: Type): Type := mk_inhabited { default: A }.
Global Arguments mk_inhabited {_} _.
Global Hint Mode inhabited + : typeclass_instances.

Require Import Coq.Lists.List. Import ListNotations.

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
