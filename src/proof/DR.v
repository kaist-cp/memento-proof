Require Import Lia.
Require Import List.
Import ListNotations.

Require Import HahnList.
Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Order.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Env.
From Memento Require Import Common.
From Memento Require Import ControlConstructCases.

Set Implicit Arguments.

Lemma read_only_statements:
  forall env envt s tr ts mmts thr_term,
    TypeSystem.judge env envt ->
    EnvType.ro_judge envt s ->
    Thread.rtc env tr (Thread.mk s [] ts mmts) thr_term [] ->
  [] ~ tr /\ mmts = thr_term.(Thread.mmts).
Proof.
  intros env envt s tr ts mmts thr_term TYPEJ ROJ. generalize tr ts mmts thr_term. induction ROJ; subst; i.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    (* eapply IHROJ. eauto. *)
    admit.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    admit.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss; destruct c_loops; inv CONT.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    admit.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    admit.
Qed.

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
    EnvType.rw_judge envt labs s ->
    (* TODO: forall function *)
  DR env s.
Proof.
  intros env envt labs s TYPEJ ENVTJ.
  induction ENVTJ; intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  - inv EX1; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    inv EX2; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    esplits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply trace_refine_eq.
    + i. splits; eauto. apply trace_refine_eq.
  - inv EX1; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    inv EX2; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    esplits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply trace_refine_eq.
    + i. splits; eauto. apply trace_refine_eq.
  - inv EX1; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    inv EX2; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    esplits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply trace_refine_eq.
    + i. splits; eauto. apply trace_refine_eq.
  - inv EX1; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss; destruct c_loops; ss. }
    inv EX2; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss; destruct c_loops; ss. }
    esplits; eauto.
    + apply Thread.rtc_refl; eauto.
    + apply trace_refine_eq.
    + i. splits; eauto. apply trace_refine_eq.
  - inversion EX1; [subst|].
    { destruct thr_term'. esplits; ss; eauto; [apply trace_refine_eq |].
      i. inv H; des; ss.
    }
    inv EX2; [|subst].
    { destruct thr_term. ss. esplits; [eauto | | |].
      - rewrite app_nil_r. apply trace_refine_eq.
      - i. splits; ss. apply trace_refine_eq.
      - i. inv H; des; ss.
    }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv ONE0. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    inv RTC0; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    rewrite app_nil_r in *. subst.
    esplits; eauto; [apply trace_refine_eq |].
    i. splits; ss. apply trace_refine_eq.
  - inversion EX1; [subst|].
    { destruct thr_term'. esplits; ss; eauto; [apply trace_refine_eq |].
      i. inv H; des; ss.
    }
    inv EX2; [|subst].
    { destruct thr_term. ss. esplits; [eauto | | |].
      - rewrite app_nil_r. apply trace_refine_eq.
      - i. splits; ss. apply trace_refine_eq.
      - i. inv H; des; ss.
    }
    inv ONE. inv NORMAL_STEP; inv STEP; ss; inv STMT.
    + inv RTC; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      inv ONE0. inv NORMAL_STEP; inv STEP; ss; inv STMT.
      { rewrite fun_add_spec in LOCAL_TIME0.
        destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])) eqn:Heq; ss; [lia |].
        admit.
        (* Equivdec false *)
      }
      { rewrite fun_add_spec in LOCAL_TIME0.
        destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])) eqn:Heq; ss; [lia |].
        admit.
        (* Equivdec false *)
      }
      inv RTC0; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      rewrite app_nil_r in *. subst. esplits; eauto.
      { apply trace_refine_eq. }
      { i. splits; ss. apply refine_empty; ss. }
      i. splits; ss. rewrite fun_add_spec.
      destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])) eqn:Heq; ss.
      admit.
      (* Equivdec false *)
    + inv RTC; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      inv ONE0. inv NORMAL_STEP; inv STEP; ss; inv STMT.
      { rewrite fun_add_spec in LOCAL_TIME0.
        destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])) eqn:Heq; ss; [lia |].
        admit.
        (* Equivdec false *)
      }
      { rewrite fun_add_spec in LOCAL_TIME0.
        destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])) eqn:Heq; ss; [lia |].
        admit.
        (* Equivdec false *)
      }
      inv RTC0; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      rewrite app_nil_r in *. subst. esplits; eauto.
      { apply trace_refine_eq. }
      { i. splits; ss. apply refine_empty; ss. }
      i. splits; ss. rewrite fun_add_spec.
      destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])) eqn:Heq; ss.
      admit.
      (* Equivdec false *)
    + inv RTC; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      inv ONE0. inv NORMAL_STEP; inv STEP; ss; inv STMT; try lia.
      inv RTC0; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      rewrite app_nil_r in *. subst. esplits; eauto.
      { apply trace_refine_eq. }
      i. splits; ss. apply refine_empty; ss.
  - inversion EX1; [subst|].
    { destruct thr_term'. esplits; ss; eauto; [apply trace_refine_eq |].
      i. inv H; des; ss.
    }
    remember EX2 as EX2'. clear HeqEX2'. inv EX2'; [|subst].
    { destruct thr_term. ss. esplits; [apply EX1 | | |].
      - rewrite app_nil_r. apply trace_refine_eq.
      - i. splits; ss. apply trace_refine_eq.
      - i. inv H; des; ss.
    }
    inv ONE. inv NORMAL_STEP; inv STEP; ss; inv STMT.
    + destruct thr_term. ss. hexploit checkpoint_cases; eauto. i. des; hexploit read_only_statements; eauto; i; des; subst; ss.
      * destruct thr_term'. esplits; eauto.
        { hexploit trace_refine_app; [apply trace_refine_eq | apply H | rewrite app_nil_l; eauto]. }
        unfold STOP. i. des; try by destruct c_pfx; ss.
        unfold Cont.Loops in H1. exploit H1.
        { instantiate (1 := Cont.chkptcont (TState.regs ts) r0 [] (mid ++ [lab])).
          rewrite in_app_iff. right. ss. left. ss.
        }
        i. des. ss.
      * inv CALL_DONE0; inv STEP; ss; inv STMT; inv THR2; rewrite <- rev_eq in CONT; repeat rewrite rev_app in CONT; ss. inv CONT.
        inv ONE0. inv NORMAL_STEP; inv STEP; inv STMT; ss.
        { hexploit Thread.step_time_mon; eauto. i. ss.
          rewrite fun_add_spec in *. destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])); ss; [lia |].
          admit.
          (* Equivdec false *)
        }
        inv RTC0; ss; cycle 1.
        { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
        esplits; eauto.
        { rewrite app_nil_r. eauto. }
        i. splits; ss; [funtac | apply trace_refine_eq].
    + inv RTC; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      inv ONE0. inv NORMAL_STEP; inv STEP; inv STMT; ss; [lia |].
      inv RTC0; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      esplits; eauto; [apply trace_refine_eq |].
      i. splits; ss. apply trace_refine_eq.
  - inversion EX1; [subst|].
    { eexists tr'. eexists thr_term'.(Thread.stmt). eexists thr_term'.(Thread.cont). eexists thr_term'.(Thread.ts).
      splits; ss.
      - destruct thr_term'; ss.
      - apply trace_refine_eq.
      - i. inv H; des; ss.
    }
    inversion EX2.
    { eexists tr. eexists thr_term.(Thread.stmt). eexists thr_term.(Thread.cont). eexists thr_term.(Thread.ts).
      subst. splits; ss.
      - destruct thr_term; ss.
      - rewrite app_nil_r. apply trace_refine_eq.
      - i. splits; ss. apply trace_refine_eq.
      - i. inv H; des; ss.
    }
    inv ONE. inversion NORMAL_STEP; inv STEP; ss. inv STMT.
    inv ONE0. inv NORMAL_STEP0; inv STEP; ss. inv STMT.
    rewrite app_nil_r in *. subst. unfold DR in *.
    destruct (EquivDec.equiv_dec (sem_expr (TState.regs ts) e) (Val.bool true)) eqn:Heq.
    + hexploit IHENVTJ1; [apply RTC | apply RTC0 |].
      i. des. eexists tr_x. eexists s_x. eexists c_x. eexists ts_x. splits; ss.
      econs 2; eauto; [econs; eauto |]; rewrite app_nil_l; ss.
    + hexploit IHENVTJ2; [apply RTC | apply RTC0 |].
      i. des. eexists tr_x. eexists s_x. eexists c_x. eexists ts_x. splits; ss.
      econs 2; eauto; [econs; eauto |]; rewrite app_nil_l; ss.
  - admit.
  - admit.
Qed.
