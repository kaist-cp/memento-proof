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

Module Cont.
  Inductive t :=
  | loopcont (rmap: VRegMap) (r: VReg) (s_body: list Stmt) (s_cont: list Stmt)
  | fncont (rmap: VRegMap) (r: VReg) (s_cont: list Stmt)
  | chkptcont (rmap: VRegMap) (r: VReg) (s_cont: list Stmt) (mid: list Label)
  .
  #[export] Hint Constructors t : semantics.
End Cont.

Module TState.
  Inductive t := mk {
    regs: VRegMap;
    time: Time.t;
  }.
  #[export] Hint Constructors t : semantics.

  (* TODO: init *)
End TState.

Module Mmt.
  Inductive t := mk {
    val: Val.t;
    time: Time.t;
  }.
End Mmt.

Module Mmts.
  Definition t := list Label -> Mmt.t.

  (* TODO: init *)
End Mmts.

Module Thread.
  Definition t := (list Stmt * list Cont.t * TState.t * Mmts.t)%type.
End Thread.

Definition Mem := PLoc.t -> Val.t.

Module Machine.
  Definition t := (list Thread.t * Mem)%type.
End Machine.

Module Event.
  Inductive t :=
  | R (l: PLoc.t) (v: Val.t)
  | U (l: PLoc.t) (old new:Val.t)
  .
End Event.
