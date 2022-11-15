Require Import ZArith.

(* From Memento Require Import Utils. *)
From Memento Require Import syntax.

Set Implicit Arguments.

Create HintDb semantics discriminated.

Module Time.
  Include Nat.
End Time.

Definition Tid := nat.

Definition VRegMap := VReg -> Val.t.

Module TState.
  Inductive t := mk {
    regs: VRegMap;
    time: Time.t;
  }.
  #[export] Hint Constructors t : semantics.

  (* TOOD: init *)
End TState.

Module Mmt.
  Inductive t := mk {
    val: Val.t;
    time: Time.t;
  }.
End Mmt.

Module Mmts.
  Definition t := list Label -> Mmt.t.

  (* TOOD: init *)
End Mmts.

(* TODO: Thread, Mem, Machine *)

Definition Mem := PLoc.t -> Val.t.

Module Event.
  Inductive t :=
  | R (l: PLoc.t) (v: Val.t)
  | U (l: PLoc.t) (old new:Val.t)
  .
End Event.
