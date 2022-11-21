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
From Memento Require Import Lifting.
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
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    split; ss. eapply refine_read; [apply trace_refine_eq |]; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    split; ss. eapply refine_read; [apply trace_refine_eq |]; ss.
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
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss.
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
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inversion RTC; ss; subst.
    { split; ss. apply trace_refine_eq. }
    rewrite app_nil_r in *.
    destruct (EquivDec.equiv_dec (sem_expr (TState.regs ts0) e0) (Val.bool true)) eqn:Heq.
    + eapply IHROJ1; eauto.
    + eapply IHROJ2; eauto.
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
    (forall f prms s_f,
      IdMap.find f envt = Some FnType.RW ->
      IdMap.find f env = Some (prms, s_f) ->
     DR env s_f
    ) ->
  DR env s.
Proof.
  intros env envt labs s TYPEJ ENVTJ.
  induction ENVTJ; intros FNJ tr tr' thr_term thr_term' ts mmts EX1 EX2.
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
    + destruct thr_term. ss.
      rewrite app_nil_r in *. subst.
      hexploit chkpt_fn_cases; [| apply RTC | | left |]; ss; eauto.
      { rewrite app_nil_l. eauto. }
      i. des; hexploit read_only_statements; eauto; i; des; subst; ss.
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
    { destruct thr_term'. esplits; ss; eauto; [apply trace_refine_eq |].
      i. inv H; des; ss.
    }
    inv EX2; [|subst].
    { destruct thr_term. ss. esplits; [eauto | | |].
      - rewrite app_nil_r. apply trace_refine_eq.
      - i. splits; ss. apply trace_refine_eq.
      - i. inv H; des; ss.
    }
    inv ONE. inversion NORMAL_STEP; inv STEP; ss. inv STMT.
    inv ONE0. inv NORMAL_STEP0; inv STEP; ss. inv STMT.
    rewrite app_nil_r in *. subst.
    rewrite ENV_F0 in *. inv ENV_F.
    hexploit FNJ; eauto. unfold DR. intro IHF.
    hexploit chkpt_fn_cases; [| apply RTC | | |]; eauto.
    { rewrite app_nil_l. ss. }
    hexploit chkpt_fn_cases; [| apply RTC0 | | |]; eauto.
    { rewrite app_nil_l. ss. }
    i. des; ss.
    + (* (ONGOING, ONGOING) *)
      destruct thr_term. destruct thr_term'. ss. subst.
      hexploit IHF; eauto. ss. i. des.
      hexploit lift_cont; eauto. ss. instantiate (1 := [Cont.fncont (TState.regs ts) r []]). intros TR_X. apply relax_base in TR_X.
      esplits; [| eauto | |].
      * econs 2; eauto; cycle 1.
        { rewrite app_nil_l. ss. }
        econs; eauto. rewrite app_nil_r. ss.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx; ss.
        hexploit H4.
        { instantiate (1 := Cont.fncont (TState.regs ts) r []).
          rewrite in_app_iff. right. ss. left. ss.
        }
        i. des. ss.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx0; ss.
        hexploit H4.
        { instantiate (1 := Cont.fncont (TState.regs ts) r []).
          rewrite in_app_iff. right. ss. left. ss.
        }
        i. des. ss.
    + (* (ONGOING, DONE) *)
      hexploit CALL_DONE3; ss. i. clear CALL_DONE3.
      destruct thr_term. destruct thr_term'. ss. subst.
      hexploit IHF; eauto. ss. i. des.
      inversion CALL_DONE0; inv STEP; ss; inv THR2; rewrite snoc_eq_snoc in CONT; des; ss. subst.
      hexploit H2.
      { unfold STOP. repeat right. esplits; ss. }
      i. des. subst.
      inv STMT. inv CONT0.
      esplits; eauto.
      * econs 2; cycle 2.
        { rewrite app_nil_l. ss. }
        { econs; eauto. ss. rewrite app_nil_r. ss. }
        hexploit lift_cont; eauto. ss. instantiate (1 := [Cont.fncont (TState.regs ts) r0 []]). intros TR_X. apply relax_base in TR_X.
        rewrite <- (app_nil_r tr_x). eapply Thread.rtc_step_trans; eauto.
        econs 2.
        { econs; eauto. rewrite app_nil_l. ss. }
        { econs; eauto. }
        ss.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx; ss.
        hexploit H4.
        { instantiate (1 := Cont.fncont (TState.regs ts) r0 []).
          rewrite in_app_iff. right. ss. left. ss.
        }
        i. des. ss.
    + (* (DONE, ONGOING) *)
      hexploit CALL_DONE3; ss. i. clear CALL_DONE3.
      destruct thr_term. destruct thr_term'. ss. subst.
      hexploit IHF; eauto. ss. i. des.
      inv CALL_DONE0; inv STEP; ss; inv THR2; rewrite snoc_eq_snoc in CONT; des; ss. subst.
      hexploit H1.
      { unfold STOP. repeat right. esplits; ss. }
      i. des. subst.
      inv STMT. inv CONT0.
      esplits; eauto.
      * hexploit trace_refine_app; [apply H7 | |]; cycle 1.
        { rewrite app_nil_r. eauto. }
        apply trace_refine_eq.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx; ss.
        hexploit H4.
        { instantiate (1 := Cont.fncont (TState.regs ts) r0 []).
          rewrite in_app_iff. right. ss. left. ss.
        }
        i. des. ss.
    + (* (DONE, DONE) *)
      hexploit CALL_DONE3; ss. hexploit CALL_DONE8; ss. i. clear CALL_DONE3 CALL_DONE8.
      destruct thr_term. destruct thr_term'. ss. subst.
      hexploit IHF; eauto. ss. i. des.
      inv CALL_DONE0; inv STEP; ss; inv THR2; rewrite snoc_eq_snoc in CONT; des; ss. subst.
      inv CALL_DONE5; inv STEP; ss; inv THR2; rewrite snoc_eq_snoc in CONT; des; ss. subst.
      hexploit H1.
      { unfold STOP. repeat right. esplits; ss. }
      hexploit H2.
      { unfold STOP. repeat right. esplits; ss. }
      i. des. subst.
      inv STMT0. inv H4. inv STMT. inv CONT0. inv CONT1.
      esplits; eauto.
      hexploit trace_refine_app; [apply H8 | |]; cycle 1.
      { rewrite app_nil_r. eauto. }
      apply trace_refine_eq.
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
    inv ONE. inversion NORMAL_STEP; inv STEP; ss. inv STMT.
    inv ONE0. inv NORMAL_STEP0; inv STEP; ss. inv STMT.
    rewrite app_nil_r in *. subst. unfold DR in *.
    destruct (EquivDec.equiv_dec (sem_expr (TState.regs ts) e) (Val.bool true)) eqn:Heq.
    + hexploit IHENVTJ1; [| apply RTC | apply RTC0 |]; ss.
      i. des. eexists tr_x. eexists s_x. eexists c_x. eexists ts_x. splits; ss.
      econs 2; eauto; [econs; eauto |]; rewrite app_nil_l; ss.
    + hexploit IHENVTJ2; [| apply RTC | apply RTC0 |]; ss.
      i. des. eexists tr_x. eexists s_x. eexists c_x. eexists ts_x. splits; ss.
      econs 2; eauto; [econs; eauto |]; rewrite app_nil_l; ss.
  - admit.
  - admit.
Qed.
