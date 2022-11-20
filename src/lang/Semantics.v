Require Import Lia.
Require Import ZArith.
Require Import EquivDec.
Require Import List.
Import ListNotations.

Require Import sflib.

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

  Inductive pload (tr: list Event.t) (thr1 thr2: t): Prop :=
  | pload_intro
      r e l v
      s2 rmap2
      (STMT: thr1.(stmt) = (stmt_pload r e) :: s2)
      (TRACE: tr = [Event.R l v])
      (EVAL: sem_expr thr1.(ts).(TState.regs) e = l)
      (RMAP: rmap2 = VRegMap.add r v thr1.(ts).(TState.regs))
      (THR2: thr2 =
              mk
                s2
                thr1.(cont)
                (TState.mk rmap2 thr1.(ts).(TState.time))
                thr1.(mmts)
      )
  .
  Hint Constructors pload : semantics.

  Inductive palloc (tr: list Event.t) (thr1 thr2: t): Prop :=
  | palloc_intro
      r e l v
      s2 rmap2
      (STMT: thr1.(stmt) = (stmt_pload r e) :: s2)
      (TRACE: tr = [Event.R l v])
      (EVAL: sem_expr thr1.(ts).(TState.regs) e = v)
      (RMAP: rmap2 = VRegMap.add r l thr1.(ts).(TState.regs))
      (THR2: thr2 =
              mk
                s2
                thr1.(cont)
                (TState.mk rmap2 thr1.(ts).(TState.time))
                thr1.(mmts)
      )
  .
  Hint Constructors palloc : semantics.

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
      rmap2
      (STMT: thr1.(stmt) = (stmt_pcas r e_loc e_old e_new mid) :: s2)
      (TRACE: tr = [])
      (LOCAL_TIME: thr1.(ts).(TState.time) < (thr1.(mmts) mid).(Mmt.time))
      (RMAP: rmap2 = VRegMap.add r (thr1.(mmts) mid).(Mmt.val) thr1.(ts).(TState.regs))
      (THR2: thr2 =
              mk
                s2
                thr1.(cont)
                (TState.mk rmap2 (thr1.(mmts) mid).(Mmt.time))
                thr1.(mmts)
      )
  .
  Hint Constructors pcas_replay : semantics.

  Inductive chkpt_call (tr: list Event.t) (thr1 thr2: t): Prop :=
  | chkpt_call_intro
      r s_c mid s
      c2
      (STMT: thr1.(stmt) = (stmt_chkpt r s_c mid) :: s)
      (TRACE: tr = [])
      (LOCAL_TIME: (thr1.(mmts) mid).(Mmt.time) <= thr1.(ts).(TState.time))
      (CONT: c2 = (Cont.chkptcont thr1.(ts).(TState.regs) r s mid) :: thr1.(cont))
      (THR2: thr2 =
              mk
                s_c
                c2
                thr1.(ts)
                thr1.(mmts)
      )
  .
  Hint Constructors chkpt_call : semantics.

  Inductive chkpt_return (tr: list Event.t) (thr1 thr2: t): Prop :=
  | chkpt_return_intro
      e s_rem r s2 mid
      c_loops c2 t v rmap rmap2 mmts2
      (STMT: thr1.(stmt) = (stmt_return e) :: s_rem)
      (TRACE: tr = [])
      (CONT: thr1.(cont) = c_loops ++ [Cont.chkptcont rmap r s2 mid] ++ c2)
      (LOOPS: Cont.Loops(c_loops))
      (NEW_TIME: thr1.(ts).(TState.time) < t)
      (RET: sem_expr thr1.(ts).(TState.regs) e = v)
      (RMAP: rmap2 = VRegMap.add r v rmap)
      (MMTS: mmts2 = fun_add mid (Mmt.mk v t) thr1.(mmts))
      (THR2: thr2 =
              mk
                s2
                c2
                (TState.mk rmap2 t)
                mmts2
      )
  .
  Hint Constructors chkpt_return : semantics.

  Inductive chkpt_replay (tr: list Event.t) (thr1 thr2: t): Prop :=
  | chkpt_replay_intro
      r s_c mid s
      rmap2
      (STMT: thr1.(stmt) = (stmt_chkpt r s_c mid) :: s)
      (TRACE: tr = [])
      (LOCAL_TIME: thr1.(ts).(TState.time) < (thr1.(mmts) mid).(Mmt.time))
      (RMAP: rmap2 = VRegMap.add r (thr1.(mmts) mid).(Mmt.val) thr1.(ts).(TState.regs))
      (THR2: thr2 =
              mk
                s
                thr1.(cont)
                (TState.mk rmap2 (thr1.(mmts) mid).(Mmt.time))
                thr1.(mmts)
      )
  .
  Hint Constructors chkpt_replay : semantics.

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

  Inductive loop (tr: list Event.t) (thr1 thr2: t): Prop :=
  | loop_intro
      r e s_body s_cont
      v c2 rmap2
      (STMT: thr1.(stmt) = (stmt_loop r e s_body) :: s_cont)
      (TRACE: tr = [])
      (EVAL: sem_expr thr1.(ts).(TState.regs) e = v)
      (CONT: c2 = (Cont.loopcont thr1.(ts).(TState.regs) r s_body s_cont) :: thr1.(cont))
      (RMAP: rmap2 = VRegMap.add r v thr1.(ts).(TState.regs))
      (THR2: thr2 =
              mk
                s_body
                c2
                (TState.mk rmap2 thr1.(ts).(TState.time))
                thr1.(mmts)
      )
  .
  Hint Constructors loop : semantics.

  Inductive continue (tr: list Event.t) (thr1 thr2: t): Prop :=
  | continue_intro
      r e s_rem rmap s_body s_cont
      v c_rem rmap2
      (STMT: thr1.(stmt) = (stmt_continue e) :: s_rem)
      (TRACE: tr = [])
      (EVAL: sem_expr thr1.(ts).(TState.regs) e = v)
      (CONT: thr1.(cont) = (Cont.loopcont rmap r s_body s_cont) :: c_rem)
      (RMAP: rmap2 = VRegMap.add r v rmap)
      (THR2: thr2 =
              mk
                s_body
                thr1.(cont)
                (TState.mk rmap2 thr1.(ts).(TState.time))
                thr1.(mmts)
      )
  .
  Hint Constructors continue : semantics.

  Inductive break (tr: list Event.t) (thr1 thr2: t): Prop :=
  | break_intro
      r s_rem rmap s_body s_cont
      c2
      (STMT: thr1.(stmt) = stmt_break :: s_rem)
      (TRACE: tr = [])
      (CONT: thr1.(cont) = (Cont.loopcont rmap r s_body s_cont) :: c2)
      (THR2: thr2 =
              mk
                s_cont
                c2
                (TState.mk rmap thr1.(ts).(TState.time))
                thr1.(mmts)
      )
  .
  Hint Constructors break : semantics.

  Inductive call (env: Env.t) (tr: list Event.t) (thr1 thr2: t): Prop :=
  | call_intro
      r f ee s
      vv prms s_f c2 rmap2
      (STMT: thr1.(stmt) = (stmt_call r f ee) :: s)
      (TRACE: tr = [])
      (EVAL: map (sem_expr thr1.(ts).(TState.regs)) ee = vv)
      (ENV_F: IdMap.find f env = Some (prms, s_f))
      (CONT: c2 = (Cont.fncont thr1.(ts).(TState.regs) r s) :: thr1.(cont))
      (RMAP: rmap2 = IdMap.empty _)
      (* TODO: prms maps vv *)
      (THR2: thr2 =
              mk
                s_f
                c2
                (TState.mk rmap2 thr1.(ts).(TState.time))
                thr1.(mmts)
      )
  .
  Hint Constructors call : semantics.

  Inductive ret (tr: list Event.t) (thr1 thr2: t): Prop :=
  | return_intro
      e s_rem rmap
      v c_loops r s2 c2 rmap2
      (STMT: thr1.(stmt) = (stmt_return e) :: s_rem)
      (TRACE: tr = [])
      (EVAL: sem_expr thr1.(ts).(TState.regs) e = v)
      (CONT: thr1.(cont) = c_loops ++ [Cont.fncont rmap r s2] ++ c2)
      (LOOPS: Cont.Loops(c_loops))
      (RMAP: rmap2 = VRegMap.add r v rmap)
      (THR2: thr2 =
              mk
                s2
                c2
                (TState.mk rmap2 thr1.(ts).(TState.time))
                thr1.(mmts)
      )
  .
  Hint Constructors ret : semantics.

  Inductive step (env: Env.t) (tr: list Event.t) (thr1 thr2: t): Prop :=
  | step_assign
      (STEP: assign tr thr1 thr2)
  | step_pcas_succ
      (STEP: pcas_succ tr thr1 thr2)
  | step_pcas_fail
      (STEP: pcas_fail tr thr1 thr2)
  | step_pcas_replay
      (STEP: pcas_replay tr thr1 thr2)
  | step_chkpt_call
      (STEP: chkpt_call tr thr1 thr2)
  | step_chkpt_return
      (STEP: chkpt_return tr thr1 thr2)
  | step_chkpt_replay
      (STEP: chkpt_replay tr thr1 thr2)
  | step_branch
      (STEP: branch tr thr1 thr2)
  | step_loop
      (STEP: loop tr thr1 thr2)
  | step_continue
      (STEP: continue tr thr1 thr2)
  | step_break
      (STEP: break tr thr1 thr2)
  | step_call
      (STEP: call env tr thr1 thr2)
  | step_return
      (STEP: ret tr thr1 thr2)
  .
  Hint Constructors step : semantics.

  Inductive step_base_cont (env: Env.t) (tr: list Event.t) (thr1 thr2: t) (c: list Cont.t): Prop :=
  | step_base_cont_intro
      c'
      (NORMAL_STEP: step env tr thr1 thr2)
      (BASE: thr2.(cont) = c' ++ c)
  .

  Inductive rtc (env: Env.t) (tr: list Event.t) (thr thr_term: t) (c: list Cont.t): Prop :=
  | rtc_refl
      (THR: thr = thr_term)
      (TRACE: tr = [])
  | rtc_trans
      tr0 thr0 tr1
      (ONE: step_base_cont env tr0 thr thr0 c)
      (RTC: rtc env tr1 thr0 thr_term c)
      (TRACE: tr = tr0 ++ tr1)
  .

  Inductive tc (env: Env.t) (tr: list Event.t) (thr thr_term: t) (c: list Cont.t): Prop :=
  | tc_intro
      tr0 thr0 tr1
      (ONE: step_base_cont env tr0 thr thr0 c)
      (RTC: rtc env tr1 thr0 thr_term c)
      (TRACE: tr = tr0 ++ tr1)
  .

  Lemma step_time_mon :
    forall env tr thr thr_term,
      rtc env tr thr thr_term [] ->
    thr.(ts).(TState.time) <= thr_term.(ts).(TState.time).
  Proof.
    i. induction H; subst; eauto.
    etrans; cycle 1; eauto.
    inv ONE. inv NORMAL_STEP; inv STEP; ss; lia.
  Qed.
End Thread.

Definition Mem := PLoc.t -> Val.t.

Module Machine.
  Definition t := (list Thread.t * Mem)%type.
End Machine.
