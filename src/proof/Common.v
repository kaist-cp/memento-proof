Require Import EquivDec.
Require Import Ensembles.
Require Import FunctionalExtensionality.
Require Import Lia.
Require Import List.
Import ListNotations.

Require Import sflib.
Require Import HahnList.

From Memento Require Import Utils.
From Memento Require Import Order.
From Memento Require Import Syntax.
From Memento Require Import Semantics.

Set Implicit Arguments.

(* Definition H.16 *)
Definition STOP (s: list Stmt) (c: list Cont.t) :=
  <<EMPTY: (s = [] /\ c = [])>>
  \/ <<BREAK: (exists s_rem, s = stmt_break :: s_rem /\ c = [])>>
  \/ <<CONTINUE: (exists s_rem e, s = (stmt_continue e) :: s_rem /\ c = [])>>
  \/ <<RETURN: (exists s_rem e, s = (stmt_return e) :: s_rem /\ (Cont.Loops c))>>
  .

(* Lemma H.17 *)
Lemma stop_no_step:
  forall env tr s1 c1 ts1 mmts1 s2 c2 ts2 mmts2,
    STOP s1 c1 ->
    Thread.step env tr (Thread.mk s1 c1 ts1 mmts1) (Thread.mk s2 c2 ts2 mmts2) ->
  False.
Proof.
  intros env tr s1 c1 ts1 mmts1 s2 c2 ts2 mmts2 STOP1 STEP.
  destruct STOP1 as [(S & C) | [(s_rem & S & C) | [(s_rem & e & S & C) | (s_rem & e & S & LOOPS)]]];
    subst; inv STEP; ss.
  - rewrite Cont.loops_app_distr in LOOPS. destruct LOOPS as [_ LOOPS]. inv LOOPS. ss.
  - rewrite Cont.loops_app_distr in LOOPS. destruct LOOPS as [_ LOOPS]. inv LOOPS. ss.
Qed.

Lemma stop_means_no_step:
  forall env tr thr thr_term,
    STOP thr.(Thread.stmt) thr.(Thread.cont) ->
    Thread.rtc env [] tr thr thr_term ->
  thr = thr_term /\ tr = [].
Proof.
  intros env tr thr thr_term STOP1 RTC. inv RTC; [split; ss|].
  exfalso. inv ONE. destruct thr as [s1 c1 ts1 mmts1].
  match goal with
  | [STEP: Thread.step _ _ _ ?thr1 |- _] => destruct thr1 as [s2 c2 ts2 mmts2]; eapply stop_no_step; eauto
  end.
Qed.

Lemma seq_sc_stop:
  forall s c s' s_p c_p,
    __guard__ (s <> [] \/ c <> []) ->
    (s, c) ++₁ s' = (s_p, c_p) ->
  STOP s c <-> STOP s_p c_p.
Proof.
  intros s c s' s_p c_p NE SC. split.
  - intro STOP1. unfold STOP in *. des; subst; ss.
    + unguard. des; ss.
    + unfold seq_sc, seq_sc_unzip in SC. ss. inv SC. right. left. eauto.
    + unfold seq_sc, seq_sc_unzip in SC. ss. inv SC. right. right. left. eauto.
    + destruct c as [|c0 c'] using rev_ind.
      * unfold seq_sc, seq_sc_unzip in SC. ss. inv SC. right. right. right. eauto.
      * clear IHc'. rewrite seq_sc_last in SC. inv SC.
        right. right. right. esplits; eauto.
        apply Cont.loops_app_distr in RETURN0. destruct RETURN0 as [L1 L2].
        apply Cont.loops_app_distr. split; ss.
        econs; ss. destruct c0; ss; inv L2; ss.
  - intro STOP1. unfold STOP in *. des; subst; ss.
    + destruct c as [|c0 c'] using rev_ind; cycle 1.
      { rewrite seq_sc_last in SC. inv SC. destruct c'; ss. }
      unguard. des; ss. unfold seq_sc, seq_sc_unzip in SC. ss. inv SC. destruct s; ss.
    + destruct c as [|c0 c'] using rev_ind; cycle 1.
      { rewrite seq_sc_last in SC. inv SC. destruct c'; ss. }
      unguard. des; ss. destruct s as [|x s]; ss.
      unfold seq_sc, seq_sc_unzip in SC. ss. inv SC. right. left. eauto.
    + destruct c as [|c0 c'] using rev_ind; cycle 1.
      { rewrite seq_sc_last in SC. inv SC. destruct c'; ss. }
      unguard. des; ss. destruct s as [|x s]; ss.
      unfold seq_sc, seq_sc_unzip in SC. ss. inv SC. right. right. left. eauto.
    + destruct c as [|c0 c'] using rev_ind.
      * unguard. des; ss. destruct s as [|x s]; ss.
        unfold seq_sc, seq_sc_unzip in SC. ss. inv SC. right. right. right. eauto.
      * clear IHc'. rewrite seq_sc_last in SC. inv SC.
        right. right. right. esplits; eauto.
        apply Cont.loops_app_distr in RETURN0. destruct RETURN0 as [L1 L2].
        apply Cont.loops_app_distr. split; ss.
        econs; ss. destruct c0; ss; inv L2; ss.
Qed.

(* Definition H.19, Figure 23 *)
Inductive trace_refine (tr1 tr2: list Event.t) : Prop :=
| refine_empty
  (EMPTY1: tr1 = [])
  (EMPTY2: tr2 = [])
| refine_both
  ev tr1' tr2'
  (REFINE: trace_refine tr1' tr2')
  (TRACE1: tr1 = tr1' ++ [ev])
  (TRACE2: tr2 = tr2' ++ [ev])
| refine_read
  l v tr2'
  (REFINE: trace_refine tr1 tr2')
  (TRACE2: tr2 = tr2' ++ [Event.R l v])
.
Hint Constructors trace_refine : proof.

Notation "tr1 ~ tr2" := (trace_refine tr1 tr2) (at level 62).

Lemma trace_refine_app :
  forall tr1 tr1' tr2 tr2',
    tr1' ~ tr2' ->
    tr1 ~ tr2 ->
  tr1 ++ tr1' ~ tr2 ++ tr2'.
Proof.
  intros tr1 tr1' tr2 tr2' H. generalize tr1 tr2. induction H; ii; subst; eauto.
  - repeat rewrite app_nil_r. eauto.
  - apply IHtrace_refine in H0. eapply refine_both; eauto; rewrite <- app_assoc; eauto.
  - apply IHtrace_refine in H0. eapply refine_read; eauto. rewrite <- app_assoc. eauto.
Qed.

Lemma trace_refine_eq :
  forall tr, tr ~ tr.
Proof.
  induction tr; [apply refine_empty; eauto |].
  replace (a :: tr) with ([a] ++ tr); eauto.
  eapply trace_refine_app; eauto.
  eapply refine_both. instantiate (1 := []). instantiate (1 := []).
  { apply refine_empty; eauto. }
  instantiate (1 := a).
  all: eauto.
Qed.

Inductive sub_read : list Event.t -> list Event.t -> Prop :=
| sub_nil
  : sub_read [] []
| sub_keep
  ev a b
  (SUB: sub_read a b)
  : sub_read (ev :: a) (ev :: b)
| sub_drop
  l v a b
  (SUB: sub_read a b)
  : sub_read a (Event.R l v :: b)
.
Hint Constructors sub_read : proof.

Lemma sub_read_refl:
  forall tr, sub_read tr tr.
Proof. induction tr; econs; ss. Qed.

Lemma sub_read_app:
  forall a b a' b',
    sub_read a b ->
    sub_read a' b' ->
  sub_read (a ++ a') (b ++ b').
Proof.
  intros a b a' b' SUB SUB'. induction SUB; ss; econs; ss.
Qed.

Lemma sub_read_trans:
  forall a b c,
    sub_read a b ->
    sub_read b c ->
  sub_read a c.
Proof.
  intros a b c AB BC. revert a AB. induction BC; i.
  - inv AB. econs.
  - inv AB.
    + econs. eauto.
    + econs. eauto.
  - econs. eauto.
Qed.

Lemma sub_read_refine:
  forall a b, sub_read a b <-> a ~ b.
Proof.
  split.
  - induction 1.
    + econs 1; ss.
    + change (ev :: a) with ([ev] ++ a). change (ev :: b) with ([ev] ++ b).
      apply trace_refine_app; ss. apply trace_refine_eq.
    + rewrite <- (app_nil_l a). change (Event.R l v :: b) with ([Event.R l v] ++ b).
      apply trace_refine_app; ss. econs 3; [econs 1|]; ss.
  - induction 1; subst.
    + econs.
    + apply sub_read_app; ss. apply sub_read_refl.
    + rewrite <- (app_nil_r tr1). apply sub_read_app; ss. econs. econs.
Qed.

Lemma trace_refine_trans:
  forall tr1 tr2 tr3,
    tr1 ~ tr2 ->
    tr2 ~ tr3 ->
  tr1 ~ tr3.
Proof.
  i. rewrite <- sub_read_refine in *. eapply sub_read_trans; eauto.
Qed.

Lemma trace_refine_nil_ins :
  forall tr tr1 tr2 tr',
    tr ~ tr1 ++ tr2 ->
    [] ~ tr' ->
  tr ~ tr1 ++ tr' ++ tr2.
Proof.
  intros tr tr1 tr2. revert tr tr1. induction tr2 using rev_ind; i; ss.
  { rewrite app_nil_r in *. rewrite <- (app_nil_r tr). apply trace_refine_app; ss. }
  inv H.
  - destruct tr1, tr2; ss.
  - rewrite app_assoc in TRACE2. rewrite snoc_eq_snoc in TRACE2. des. subst.
    econs 2; cycle 2.
    { rewrite app_assoc. rewrite app_assoc. ss. }
    all: ss.
    rewrite <- app_assoc. apply IHtr2; ss.
  - rewrite app_assoc in TRACE2. rewrite snoc_eq_snoc in TRACE2. des. subst.
    econs 3; cycle 1.
    { rewrite app_assoc. rewrite app_assoc. ss. }
    rewrite <- app_assoc. apply IHtr2; ss.
Qed.

(* Definition H.6 *)
Inductive mmt_id_exp (mid_pfx: list Label) (labs: Ensemble Label) : Ensemble (list Label) :=
| mmt_id_exp_intro
  lab mid mid_sfx
  (LAB: Ensembles.In _ labs lab)
  (MID: mid = mid_pfx ++ [lab] ++ mid_sfx)
  : Ensembles.In _ (mmt_id_exp mid_pfx labs) mid
.

Lemma exp_disj_pres:
  forall mids0 mids1 pfx,
    Disjoint _ mids0 mids1 ->
  Disjoint _ (mmt_id_exp pfx mids0) (mmt_id_exp pfx mids1).
Proof.
  i. econs. ii. inv H0. inv H1. inv H2.
  apply app_inv_head in MID. inv MID.
  inv H. specialize H0 with lab0. apply H0. econs; ss.
Qed.

Lemma rtc_nil_inv:
  forall env tr thr thr_term,
    Thread.rtc env [] tr thr thr_term ->
  (tr = [] /\ thr_term = thr)
  \/ (exists tr0 tr1 thr0,
        tr = tr0 ++ tr1
        /\ Thread.step env tr0 thr thr0
        /\ Thread.rtc env [] tr1 thr0 thr_term).
Proof.
  intros env tr thr thr_term RTC. inv RTC; [left | right]; ss.
  inv ONE. esplits; eauto.
Qed.

Lemma tc_nil_inv:
  forall env tr thr thr_term,
    Thread.tc env [] tr thr thr_term ->
  exists tr0 tr1 thr0,
    tr = tr0 ++ tr1
    /\ Thread.step env tr0 thr thr0
    /\ Thread.rtc env [] tr1 thr0 thr_term.
Proof.
  intros env tr thr thr_term TC. inv TC. inv ONE. esplits; eauto.
Qed.

Lemma tc_rtc:
  forall env c tr thr thr_term,
    Thread.tc env c tr thr thr_term ->
  Thread.rtc env c tr thr thr_term.
Proof. intros env c tr thr thr_term TC. inv TC. econs 2; eauto. Qed.

Lemma rtc_app:
  forall env c tr tr1 tr2 thr1 thr2 thr3,
    Thread.rtc env c tr1 thr1 thr2 ->
    Thread.rtc env c tr2 thr2 thr3 ->
    tr = tr1 ++ tr2 ->
  Thread.rtc env c tr thr1 thr3.
Proof. i. subst. eapply Thread.rtc_trans; eauto. Qed.

Lemma rtc_step:
  forall env c tr tr0 tr1 thr thr0 thr_term c0,
    Thread.step env tr0 thr thr0 ->
    thr0.(Thread.cont) = c0 ++ c ->
    Thread.rtc env c tr1 thr0 thr_term ->
    tr = tr0 ++ tr1 ->
  Thread.rtc env c tr thr thr_term.
Proof.
  intros env c tr tr0 tr1 thr thr0 thr_term c0 STEP BASE RTC TR.
  eapply Thread.rtc_tc; [econs; [exact STEP | exact BASE] | exact RTC | exact TR].
Qed.

Lemma rtc_nil_step:
  forall env tr tr0 tr1 thr thr0 thr_term,
    Thread.step env tr0 thr thr0 ->
    Thread.rtc env [] tr1 thr0 thr_term ->
    tr = tr0 ++ tr1 ->
  Thread.rtc env [] tr thr thr_term.
Proof.
  intros env tr tr0 tr1 thr thr0 thr_term STEP RTC TR.
  eapply rtc_step; [exact STEP | rewrite app_nil_r; reflexivity | exact RTC | exact TR].
Qed.

Lemma rtc_one:
  forall env tr thr thr',
    Thread.step env tr thr thr' ->
  Thread.rtc env [] tr thr thr'.
Proof.
  intros env tr thr thr' STEP. eapply rtc_nil_step; [exact STEP | econs | rewrite app_nil_r; ss].
Qed.

Lemma step_assign_inv:
  forall env tr r e s c ts mmts thr',
    Thread.step env tr (Thread.mk (stmt_assign r e :: s) c ts mmts) thr' ->
  tr = []
  /\ exists v,
      sem_expr ts.(TState.regs) e = Some v
      /\ thr' = Thread.mk s c (TState.mk (VRegMap.add r v ts.(TState.regs)) ts.(TState.time)) mmts.
Proof. i. inv H. esplits; eauto. Qed.

Lemma step_if_inv:
  forall env tr e s_t s_f s c ts mmts thr',
    Thread.step env tr (Thread.mk (stmt_if e s_t s_f :: s) c ts mmts) thr' ->
  tr = []
  /\ exists b,
      sem_expr ts.(TState.regs) e = Some (Val.bool b)
      /\ thr' = Thread.mk ((if b then s_t else s_f) ++ s) c ts mmts.
Proof. i. inv H. esplits; eauto. Qed.

Lemma step_loop_inv:
  forall env tr r e s_body s c ts mmts thr',
    Thread.step env tr (Thread.mk (stmt_loop r e s_body :: s) c ts mmts) thr' ->
  tr = []
  /\ exists v,
      sem_expr ts.(TState.regs) e = Some v
      /\ thr' = Thread.mk s_body (Cont.loopcont ts.(TState.regs) r s_body s :: c)
                  (TState.mk (set_opt r v ts.(TState.regs)) ts.(TState.time)) mmts.
Proof. i. inv H. esplits; eauto. Qed.

Lemma step_continue_inv:
  forall env tr e s c ts mmts thr',
    Thread.step env tr (Thread.mk (stmt_continue e :: s) c ts mmts) thr' ->
  tr = []
  /\ exists v rmap r s_body s_cont c',
      sem_expr ts.(TState.regs) e = Some v
      /\ c = Cont.loopcont rmap r s_body s_cont :: c'
      /\ thr' = Thread.mk s_body c (TState.mk (set_opt r v rmap) ts.(TState.time)) mmts.
Proof. i. inv H. esplits; eauto. Qed.

Lemma step_break_inv:
  forall env tr s c ts mmts thr',
    Thread.step env tr (Thread.mk (stmt_break :: s) c ts mmts) thr' ->
  tr = []
  /\ exists rmap r s_body s_cont c',
      c = Cont.loopcont rmap r s_body s_cont :: c'
      /\ thr' = Thread.mk s_cont c' (TState.mk rmap ts.(TState.time)) mmts.
Proof. i. inv H. esplits; eauto. Qed.

Lemma step_call_inv:
  forall env tr r f es s c ts mmts thr',
    Thread.step env tr (Thread.mk (stmt_call r f es :: s) c ts mmts) thr' ->
  tr = []
  /\ exists vs prms s_f,
      sem_exprs ts.(TState.regs) es = Some vs
      /\ IdMap.find f env = Some (prms, s_f)
      /\ length prms = length vs
      /\ thr' = Thread.mk s_f (Cont.fncont ts.(TState.regs) r s :: c)
                  (TState.mk (bind_params prms vs) ts.(TState.time)) mmts.
Proof. i. inv H. esplits; eauto. Qed.

Lemma step_chkpt_inv:
  forall env tr r s_c e_mid s c ts mmts thr',
    Thread.step env tr (Thread.mk (stmt_chkpt r s_c e_mid :: s) c ts mmts) thr' ->
  tr = []
  /\ exists m,
      sem_expr ts.(TState.regs) e_mid = Some (Val.mid m)
      /\ (((mmts m).(Mmt.time) <= ts.(TState.time)
           /\ thr' = Thread.mk s_c (Cont.chkptcont ts.(TState.regs) r s m :: c) ts mmts)
          \/ (ts.(TState.time) < (mmts m).(Mmt.time)
             /\ thr' = Thread.mk s c
                         (TState.mk (VRegMap.add r (mmts m).(Mmt.val) ts.(TState.regs)) (mmts m).(Mmt.time))
                         mmts)).
Proof. i. inv H; (split; [ss|]); esplits; eauto. Qed.

Lemma step_pcas_inv:
  forall env tr r e_loc e_old e_new e_mid s c ts mmts thr',
    Thread.step env tr (Thread.mk (stmt_pcas r e_loc e_old e_new e_mid :: s) c ts mmts) thr' ->
  (exists m v_r t,
      sem_expr ts.(TState.regs) e_mid = Some (Val.mid m)
      /\ (mmts m).(Mmt.time) <= ts.(TState.time)
      /\ ts.(TState.time) < t
      /\ thr' = Thread.mk s c (TState.mk (VRegMap.add r v_r ts.(TState.regs)) t)
                  (fun_add m (Mmt.mk v_r t) mmts))
  \/ (exists m,
      sem_expr ts.(TState.regs) e_mid = Some (Val.mid m)
      /\ ts.(TState.time) < (mmts m).(Mmt.time)
      /\ tr = []
      /\ thr' = Thread.mk s c
                  (TState.mk (VRegMap.add r (mmts m).(Mmt.val) ts.(TState.regs)) (mmts m).(Mmt.time))
                  mmts).
Proof. i. inv H; [left | left | right]; esplits; eauto. Qed.

Lemma step_return_inv:
  forall env tr e s_rem c_loops f c ts mmts thr',
    Thread.step env tr (Thread.mk (stmt_return e :: s_rem) (c_loops ++ f :: c) ts mmts) thr' ->
    Cont.Loops c_loops ->
    ~ Cont.Loops [f] ->
  tr = []
  /\ exists v,
      sem_expr ts.(TState.regs) e = Some v
      /\ match f with
         | Cont.fncont rmap r s2 =>
             thr' = Thread.mk s2 c (TState.mk (VRegMap.add r v rmap) ts.(TState.time)) mmts
         | Cont.chkptcont rmap r s2 m =>
             exists t,
               ts.(TState.time) < t
               /\ thr' = Thread.mk s2 c (TState.mk (VRegMap.add r v rmap) t) (fun_add m (Mmt.mk v t) mmts)
         | Cont.loopcont _ _ _ _ => False
         end.
Proof.
  intros env tr e s_rem c_loops f c ts mmts thr' STEP LOOPS_C NLOOP.
  inv STEP.
  - hexploit Cont.loops_base_cont_eq; [exact LOOPS_C | exact LOOPS | exact NLOOP | | exact CONT |].
    { intro L. inv L. ss. }
    intro EQ. inv EQ. split; ss. esplits; eauto.
  - hexploit Cont.loops_base_cont_eq; [exact LOOPS_C | exact LOOPS | exact NLOOP | | exact CONT |].
    { intro L. inv L. ss. }
    intro EQ. inv EQ. split; ss. esplits; eauto.
Qed.

Lemma chkpt_replay_forced:
  forall env tr r s_c e_mid s c ts mmts m thr',
    Thread.step env tr (Thread.mk (stmt_chkpt r s_c e_mid :: s) c ts mmts) thr' ->
    sem_expr ts.(TState.regs) e_mid = Some (Val.mid m) ->
    ts.(TState.time) < (mmts m).(Mmt.time) ->
  tr = []
  /\ thr' = Thread.mk s c
              (TState.mk (VRegMap.add r (mmts m).(Mmt.val) ts.(TState.regs)) (mmts m).(Mmt.time))
              mmts.
Proof.
  intros env tr r s_c e_mid s c ts mmts m thr' STEP EVAL LT.
  destruct (step_chkpt_inv STEP) as [TR (m' & EVAL' & [(LE & _) | (_ & THR)])];
    rewrite EVAL in EVAL'; inv EVAL'; [lia | ss].
Qed.

Lemma pcas_replay_forced:
  forall env tr r e_loc e_old e_new e_mid s c ts mmts m thr',
    Thread.step env tr (Thread.mk (stmt_pcas r e_loc e_old e_new e_mid :: s) c ts mmts) thr' ->
    sem_expr ts.(TState.regs) e_mid = Some (Val.mid m) ->
    ts.(TState.time) < (mmts m).(Mmt.time) ->
  tr = []
  /\ thr' = Thread.mk s c
              (TState.mk (VRegMap.add r (mmts m).(Mmt.val) ts.(TState.regs)) (mmts m).(Mmt.time))
              mmts.
Proof.
  intros env tr r e_loc e_old e_new e_mid s c ts mmts m thr' STEP EVAL LT.
  destruct (step_pcas_inv STEP) as [(m' & v_r & t & EVAL' & LE & _ & _) | (m' & EVAL' & _ & TR & THR)];
    rewrite EVAL in EVAL'; inv EVAL'; [lia | ss].
Qed.

Lemma STOP_app_loop:
  forall s c c',
    STOP s (c ++ [c']) ->
  STOP s c.
Proof.
  intros s c c' STOP_S.
  destruct STOP_S as [(_ & C) | [(s_rem & _ & C) | [(s_rem & e & _ & C) | (s_rem & e & S & LOOPS)]]];
    try by destruct c; ss.
  right. right. right. exists s_rem, e. split; ss.
  apply Cont.loops_app_distr in LOOPS. destruct LOOPS as [LOOPS _]. ss.
Qed.

Lemma STOP_app_nonloop:
  forall s c c',
    STOP s (c ++ [c']) ->
    ~ Cont.Loops [c'] ->
  False.
Proof.
  intros s c c' STOP_S NLOOP.
  destruct STOP_S as [(_ & C) | [(s_rem & _ & C) | [(s_rem & e & _ & C) | (s_rem & e & S & LOOPS)]]];
    try by destruct c; ss.
  apply Cont.loops_app_distr in LOOPS. destruct LOOPS as [_ LOOPS]. contradiction.
Qed.
