Require Import List.
Import ListNotations.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Env.
From Memento Require Import Common.

Set Implicit Arguments.

Definition DR (env: Env.t) (s: list Stmt) :=
  forall tr tr' thr thr' thr_term thr_term' ts mmts,
    thr = Thread.mk s [] ts mmts ->
    thr' = Thread.mk s [] ts thr_term.(Thread.mmts) ->
    Thread.rtc env tr thr thr_term [] ->
    Thread.rtc env tr' thr' thr_term' [] ->
  exists tr_x s_x c_x ts_x,
    Thread.rtc env tr_x thr (Thread.mk s_x c_x ts_x thr_term'.(Thread.mmts)) []
    /\ tr_x ~ tr ++ tr'
    /\ (STOP thr_term.(Thread.stmt) thr_term.(Thread.cont) ->
          thr_term.(Thread.stmt) = s_x
          /\ thr_term.(Thread.cont) = c_x
          /\ thr_term.(Thread.ts) = ts_x
          /\ thr_term.(Thread.mmts) = thr_term'.(Thread.mmts)
          /\ [] ~ tr')
    /\ (STOP thr_term'.(Thread.stmt) thr_term'.(Thread.cont) ->
          thr_term'.(Thread.stmt) = s_x
          /\ thr_term'.(Thread.cont) = c_x
          /\ thr_term'.(Thread.ts) = ts_x)
  .

Lemma DR_RW :
  forall env envt labs s,
    TypeSystem.judge env envt ->
    EnvType.judge envt labs s ->
    (* TODO: forall function *)
  DR env s.
Proof.
  intros env envt labs s TYPEJ ENVTJ.
  intros tr tr' thr thr' thr_term thr_term' ts mmts THR THR' EX1 EX2.
  induction ENVTJ.
  - eexists []. eexists s. eexists []. eexists ts.
    inv EX1; ss; cycle 1.
    { inv STEP. inv STEP0. inv STEP. ss. }
    inv EX2; ss; cycle 1.
    { inv STEP. inv STEP0. inv STEP. ss. }
    splits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply refine_empty; eauto.
    + i. splits; eauto. apply refine_empty; eauto.
  - eexists []. eexists s. eexists []. eexists ts.
    inv EX1; ss; cycle 1.
    { inv STEP. inv STEP0. inv STEP. ss. }
    inv EX2; ss; cycle 1.
    { inv STEP. inv STEP0. inv STEP. ss. }
    splits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply refine_empty; eauto.
    + i. splits; eauto. apply refine_empty; eauto.
  - eexists []. eexists s. eexists []. eexists ts.
    inv EX1; ss; cycle 1.
    { inv STEP. inv STEP0. inv STEP. ss. }
    inv EX2; ss; cycle 1.
    { inv STEP. inv STEP0. inv STEP. ss. }
    splits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply refine_empty; eauto.
    + i. splits; eauto. apply refine_empty; eauto.
  - eexists []. eexists s. eexists []. eexists ts.
    inv EX1; ss; cycle 1.
    { inv STEP. inv STEP0. inv STEP. ss. }
    inv EX2; ss; cycle 1.
    { inv STEP. inv STEP0. inv STEP. ss. }
    splits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply refine_empty; eauto.
    + i. splits; eauto. apply refine_empty; eauto.
  - admit.
  - admit.
Qed.
