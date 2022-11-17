Require Import ZArith.
Require Import EquivDec.
Require Import List.
Import ListNotations.

From Memento Require Import Utils.
From Memento Require Import Order.
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
    | None => Val.int 0
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
  Hint Constructors t : semantics.

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
  Hint Constructors t : semantics.

  (* TODO: init *)
End TState.

Module Mmt.
  Inductive t := mk {
    val: Val.t;
    time: Time.t;
  }.
  Hint Constructors t : semantics.
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
  Hint Constructors t : semantics.
End Event.

Module Thread.
  Inductive t := mk {
    stmt: list Stmt;
    cont: list Cont.t;
    ts: TState.t;
    mmts: Mmts.t;
  }.
  Hint Constructors t : semantics.

  Inductive assign (tr: list Event.t) (thr1 thr2: t): Prop :=
  | assign_intro
      r e v
      s2 rmap2
      (STMT: thr1.(stmt) = (stmt_assign r e) :: s2)
      (TRACE: tr = [])
      (EVAL: sem_expr thr1.(ts).(TState.regs) e = v)
      (RMAP: rmap2 = VRegMap.add r v thr1.(ts).(TState.regs))
      (THR2: thr2 =
              mk
                s2
                thr1.(cont)
                (TState.mk rmap2 thr1.(ts).(TState.time))
                thr1.(mmts)
      )
  .
  Hint Constructors assign : semantics.

  Inductive pcas_succ (tr: list Event.t) (thr1 thr2: t): Prop :=
  | pcas_succ_intro
      r e_loc e_old e_new mid s2
      l v_old v_new v_r t rmap2 mmts2
      (STMT: thr1.(stmt) = (stmt_pcas r e_loc e_old e_new mid) :: s2)
      (TRACE: tr = [Event.U l v_old v_new])
      (LOC: sem_expr thr1.(ts).(TState.regs) e_loc = l)
      (OLD: sem_expr thr1.(ts).(TState.regs) e_old = v_old)
      (NEW: sem_expr thr1.(ts).(TState.regs) e_new = v_new)
      (RET: v_r = Val.tuple (Val.bool true, v_old))
      (LOCAL_TIME: (thr1.(mmts) mid).(Mmt.time) <= thr1.(ts).(TState.time))
      (NEW_TIME: thr1.(ts).(TState.time) < t)
      (RMAP: rmap2 = VRegMap.add r v_r thr1.(ts).(TState.regs))
      (MMTS: mmts2 = fun_add mid (Mmt.mk v_r t) thr1.(mmts))
      (THR2: thr2 =
              mk
                s2
                thr1.(cont)
                (TState.mk rmap2 t)
                mmts2
      )
  .
  Hint Constructors pcas_succ : semantics.

  Inductive pcas_fail (tr: list Event.t) (thr1 thr2: t): Prop :=
  | pcas_fail_intro
      r e_loc e_old e_new mid s2
      l v_old v v_r t rmap2 mmts2
      (STMT: thr1.(stmt) = (stmt_pcas r e_loc e_old e_new mid) :: s2)
      (TRACE: tr = [Event.R l v])
      (LOC: sem_expr thr1.(ts).(TState.regs) e_loc = l)
      (OLD: sem_expr thr1.(ts).(TState.regs) e_old = v_old)
      (NE: v <> v_old)
      (RET: v_r = Val.tuple (Val.bool false, v_old))
      (LOCAL_TIME: (thr1.(mmts) mid).(Mmt.time) <= thr1.(ts).(TState.time))
      (NEW_TIME: thr1.(ts).(TState.time) < t)
      (RMAP: rmap2 = VRegMap.add r v_r thr1.(ts).(TState.regs))
      (MMTS: mmts2 = fun_add mid (Mmt.mk v_r t) thr1.(mmts))
      (THR2: thr2 =
              mk
                s2
                thr1.(cont)
                (TState.mk rmap2 t)
                mmts2
      )
  .
  Hint Constructors pcas_fail : semantics.

  Inductive pcas_replay (tr: list Event.t) (thr1 thr2: t): Prop :=
  | pcas_replay_intro
      r e_loc e_old e_new mid s2
      v_r rmap2
      (STMT: thr1.(stmt) = (stmt_pcas r e_loc e_old e_new mid) :: s2)
      (TRACE: tr = [])
      (RET: v_r = (thr1.(mmts) mid).(Mmt.val))
      (LOCAL_TIME: thr1.(ts).(TState.time) < (thr1.(mmts) mid).(Mmt.time))
      (RMAP: rmap2 = VRegMap.add r v_r thr1.(ts).(TState.regs))
      (THR2: thr2 =
              mk
                s2
                thr1.(cont)
                (TState.mk rmap2 (thr1.(mmts) mid).(Mmt.time))
                thr1.(mmts)
      )
  .
  Hint Constructors pcas_replay : semantics.

  (* TODO: Fix eqdec *)
  Inductive branch (tr: list Event.t) (thr1 thr2: t): Prop :=
  | branch_intro
      e s_t s_f s
      v s_d
      (STMT: thr1.(stmt) = (stmt_if e s_t s_f) :: s)
      (TRACE: tr = [])
      (EVAL: sem_expr thr1.(ts).(TState.regs) e = v)
      (ITE: s_d = if v == Val.bool true then s_t else s_f)
      (THR2: thr2 =
              mk
                (s_d ++ s)
                thr1.(cont)
                thr1.(ts)
                thr1.(mmts)
      )
  .
  Hint Constructors branch : semantics.

  Inductive step (env: Env.t) (tr: list Event.t) (thr1 thr2: t): Prop :=
  | step_assign
      (STEP: assign tr thr1 thr2)
  | step_pcas_succ
      (STEP: pcas_succ tr thr1 thr2)
  | step_pcas_fail
      (STEP: pcas_fail tr thr1 thr2)
  | step_pcas_replay
      (STEP: pcas_replay tr thr1 thr2)
  | step_branch
      (STEP: branch tr thr1 thr2)

  (* TODO: Define other steps *)
  .
  Hint Constructors step : semantics.

  Inductive step_base_cont (env: Env.t) (tr: list Event.t) (thr1 thr2: t) (c: list Cont.t): Prop :=
  | step_base_cont_intro
      c'
      (NORMAL_STEP: step env tr thr1 thr2)
      (BASE: thr2.(cont) = c' ++ c)
  .

  Inductive rtc (env: Env.t) (tr: list Event.t) (thr1 thr2: t) (c: list Cont.t): Prop :=
  | rtc_refl
      (THR: thr1 = thr2)
      (TRACE: tr = [])
  | rtc_trans
      tr' thr' tr''
      (ONE: step_base_cont env tr' thr1 thr' c)
      (RTC: rtc env tr'' thr' thr2 c)
      (TRACE: tr = tr' ++ tr'')
  .

  Inductive tc (env: Env.t) (tr: list Event.t) (thr1 thr2: t) (c: list Cont.t): Prop :=
  | tc_intro
      tr' thr' tr''
      (ONE: step_base_cont env tr' thr1 thr' c)
      (RTC: rtc env tr'' thr' thr2 c)
      (TRACE: tr = tr' ++ tr'')
  .
End Thread.

Definition Mem := PLoc.t -> Val.t.

Module Machine.
  Definition t := (list Thread.t * Mem)%type.
End Machine.
