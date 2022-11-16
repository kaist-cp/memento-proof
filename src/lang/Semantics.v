Require Import ZArith.
Require Import List.
Import ListNotations.

From Memento Require Import Utils.
From Memento Require Import Syntax.

Set Implicit Arguments.

Create HintDb semantics discriminated.

Module Time.
  Include Nat.
End Time.

Definition Tid := nat.

Module VRegMap.
  Definition t := IdMap.t Val.t.

  Definition find (reg:Id.t) (rmap:t): Val.t :=
    match IdMap.find reg rmap with
    | Some v => v
    | None => 0
    end.

  Definition add (reg: Id.t) (val: Val.t) (rmap: t): t :=
    IdMap.add reg val rmap.
End VRegMap.

Definition sem_expr (rmap: VRegMap.t) (e: Expr): Val.t :=
  match e with
  | expr_const const => const
  | expr_reg reg => VRegMap.find reg rmap
  end.

Module Cont.
  Inductive t :=
  | loopcont (rmap: VRegMap.t) (r: VReg) (s_body: list Stmt) (s_cont: list Stmt)
  | fncont (rmap: VRegMap.t) (r: VReg) (s_cont: list Stmt)
  | chkptcont (rmap: VRegMap.t) (r: VReg) (s_cont: list Stmt) (mid: list Label)
  .
  #[export] Hint Constructors t : semantics.

  Definition Loops (c_loops: list t) :=
    forall c,
    List.In c c_loops ->
      exists rmap r s_body s_cont,
      c = loopcont rmap r s_body s_cont.
End Cont.

Module TState.
  Inductive t := mk {
    regs: VRegMap.t;
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
  #[export] Hint Constructors t : semantics.
End Mmt.

Module Mmts.
  Definition t := list Label -> Mmt.t.

  (* TODO: init *)
End Mmts.

Module Event.
  Inductive t :=
  | R (l: PLoc.t) (v: Val.t)
  | U (l: PLoc.t) (old new:Val.t)
  .
  #[export] Hint Constructors t : semantics.
End Event.

Module Thread.
  Inductive t := mk {
    stmt: list Stmt;
    cont: list Cont.t;
    ts: TState.t;
    mmts: Mmts.t;
  }.
  #[export] Hint Constructors t : semantics.

  Inductive assign (thr1 thr2: t): Prop :=
  | assign_intro
      r e v
      s2 rmap2
      (STMT: thr1.(stmt) = (stmt_assign r e) :: s2)
      (EVAL: sem_expr thr1.(ts).(TState.regs) e = v)
      (RMAP: rmap2 = VRegMap.add r v thr1.(ts).(TState.regs))
      (THR2: thr2 =
              mk
                s2
                thr2.(cont)
                (TState.mk rmap2 thr1.(ts).(TState.time))
                thr2.(mmts)
      )
  .
  #[export] Hint Constructors assign : semantics.

  Inductive step (tr: list Event.t) (thr1 thr2: t): Prop :=
  | step_assign
      (TRACE: tr = [])
      (STEP: assign thr1 thr2)

  (* TODO: Define other steps *)
  .
  #[export] Hint Constructors step : semantics.
End Thread.

Definition Mem := PLoc.t -> Val.t.

Module Machine.
  Definition t := (list Thread.t * Mem)%type.
End Machine.
