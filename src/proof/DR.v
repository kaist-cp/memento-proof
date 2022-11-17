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
  forall tr tr' thr_term thr_term' ts mmts,
    Thread.rtc env tr (Thread.mk s [] ts mmts) thr_term [] ->
    Thread.rtc env tr' (Thread.mk s [] ts thr_term.(Thread.mmts)) thr_term' [] ->
  exists tr_x s_x c_x ts_x,
    Thread.rtc env tr_x (Thread.mk s [] ts mmts) (Thread.mk s_x c_x ts_x thr_term'.(Thread.mmts)) []
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
  induction ENVTJ; intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  - eexists []. eexists s. eexists []. eexists ts.
    inv EX1; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    inv EX2; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    splits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply refine_empty; eauto.
    + i. splits; eauto. apply refine_empty; eauto.
  - eexists []. eexists s. eexists []. eexists ts.
    inv EX1; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    inv EX2; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    splits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply refine_empty; eauto.
    + i. splits; eauto. apply refine_empty; eauto.
  - eexists []. eexists s. eexists []. eexists ts.
    inv EX1; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    inv EX2; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    splits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply refine_empty; eauto.
    + i. splits; eauto. apply refine_empty; eauto.
  - eexists []. eexists s. eexists []. eexists ts.
    inv EX1; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    inv EX2; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    splits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply refine_empty; eauto.
    + i. splits; eauto. apply refine_empty; eauto.
  - inversion EX1; [subst|].
    { eexists tr'. eexists thr_term'.(Thread.stmt). eexists thr_term'.(Thread.cont). eexists thr_term'.(Thread.ts).
      splits; ss.
      - destruct thr_term'; ss.
      - apply trace_refine_eq.
      - i. inv H; des; ss.
    }
    inversion EX2; [|subst].
    { eexists tr. eexists thr_term.(Thread.stmt). eexists thr_term.(Thread.cont). eexists thr_term.(Thread.ts).
      subst. splits; ss.
      - destruct thr_term; ss.
      - rewrite app_nil_r. apply trace_refine_eq.
      - i. splits; ss. apply refine_empty; eauto.
      - i. inv H; des; ss.
    }
    eexists []. eexists []. eexists []. eexists thr_term.(Thread.ts).
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv ONE0. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    inv RTC0; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    rewrite app_nil_r in *. subst. splits; ss.
    { apply refine_empty; eauto. }
    i. splits; ss. apply refine_empty; eauto.
  - admit.
  - admit.
Qed.
