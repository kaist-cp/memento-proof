Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import sflib.
Require Import HahnList.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Env.

Set Implicit Arguments.

Definition STOP (s: list Stmt) (c: list Cont.t) :=
  <<EMPTY: (s = [] /\ c = [])>>
  \/ <<BREAK: (exists s_rem, s = stmt_break :: s_rem /\ c = [])>>
  \/ <<CONTINUE: (exists s_rem e, s = (stmt_continue e) :: s_rem /\ c = [])>>
  \/ <<RETURN: (exists s_rem e, s = (stmt_return e) :: s_rem /\ (Cont.Loops c))>>
  .

Lemma stop_means_no_step :
  forall env tr thr thr_term,
    STOP thr.(Thread.stmt) thr.(Thread.cont) ->
    Thread.rtc env [] tr thr thr_term ->
  thr = thr_term /\ tr = [].
Proof.
  i. inv H0; ss.
  destruct thr. ss. unfold STOP in H. des; subst.
  all: inv ONE.
  all: inv NORMAL_STEP; inv STEP; inv STMT; ss.
  - rewrite app_nil_r in *. subst.
    unfold Cont.Loops in RETURN0. hexploit RETURN0; cycle 1.
    { instantiate (1 := Cont.chkptcont rmap r s2 mid). i. des. ss. }
    apply in_app_r. ss. left. ss.
  - rewrite app_nil_r in *. subst.
    unfold Cont.Loops in RETURN0. hexploit RETURN0; cycle 1.
    { instantiate (1 := Cont.fncont rmap r s2). i. des. ss. }
    apply in_app_r. ss. left. ss.
Qed.

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

Lemma trace_refine_nil_ins :
  forall tr tr1 tr2 tr',
    tr ~ tr1 ++ tr2 ->
    [] ~ tr' ->
  tr ~ tr1 ++ tr' ++ tr2.
Proof.
  intros tr tr1 tr2. revert tr tr1. induction tr2 using rev_ind; i; ss.
  { admit. }
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

Inductive mmt_id_exp (mid_pfx: list Label) (labs: Ensemble Label) : Ensemble (list Label) :=
| mmt_id_exp_intro
  lab mid mid_sfx
  (LAB: Ensembles.In _ labs lab)
  (MID: mid = mid_pfx ++ [lab] ++ mid_sfx)
  : Ensembles.In _ (mmt_id_exp mid_pfx labs) mid
.
