Require Import List.
Import ListNotations.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Env.

Set Implicit Arguments.

Definition STOP (s: list Stmt) (c: list Cont.t) :=
  (s = [] /\ c = [])
  \/ (exists s_rem, s = stmt_break :: s_rem /\ c = [])
  \/ (exists s_rem e, s = (stmt_continue e) :: s_rem /\ c = [])
  \/ (exists s_rem e, s = (stmt_return e) :: s_rem /\ (Cont.Loops c))
  .

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
