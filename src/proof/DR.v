Require Import EquivDec.
Require Import Ensembles.
Require Import FunctionalExtensionality.
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

Set Implicit Arguments.


Definition DR (env: Env.t) (s: list Stmt) :=
  forall tr tr' thr_term thr_term' ts mmts,
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
    Thread.rtc env [] tr' (Thread.mk s [] ts thr_term.(Thread.mmts)) thr_term' ->
  exists tr_x s_x c_x ts_x,
    <<TRACE: Thread.rtc env [] tr_x (Thread.mk s [] ts mmts) (Thread.mk s_x c_x ts_x thr_term'.(Thread.mmts))>>
    /\ <<REFINEMENT: tr_x ~ tr ++ tr'>>
    /\ <<STOP_FST:
          (STOP thr_term.(Thread.stmt) thr_term.(Thread.cont) ->
          thr_term.(Thread.stmt) = s_x
          /\ thr_term.(Thread.cont) = c_x
          /\ thr_term.(Thread.ts) = ts_x
          /\ thr_term.(Thread.mmts) = thr_term'.(Thread.mmts)
          /\ [] ~ tr')>>
    /\ <<STOP_SND:
          (STOP thr_term'.(Thread.stmt) thr_term'.(Thread.cont) ->
          thr_term'.(Thread.stmt) = s_x
          /\ thr_term'.(Thread.cont) = c_x
          /\ thr_term'.(Thread.ts) = ts_x)>>
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
      { rewrite fun_add_spec in MMT0.
        destruct (TState.mid ts ++ [lab] == TState.mid ts ++ [lab]); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss. lia.
      }
      { rewrite fun_add_spec in MMT0.
        destruct (TState.mid ts ++ [lab] == TState.mid ts ++ [lab]); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss. lia.
      }
      inv RTC0; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      rewrite app_nil_r in *. subst. esplits; eauto.
      { apply trace_refine_eq. }
      { i. splits; ss. apply refine_empty; ss. }
      i. splits; ss. rewrite fun_add_spec in MMT0.
      destruct (TState.mid ts ++ [lab] == TState.mid ts ++ [lab]); cycle 1.
      { exfalso. apply c. ss. }
      inv MMT0. ss.
    + inv RTC; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      inv ONE0. inv NORMAL_STEP; inv STEP; ss; inv STMT.
      { rewrite fun_add_spec in MMT0.
        destruct (TState.mid ts ++ [lab] == TState.mid ts ++ [lab]); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss. lia.
      }
      { rewrite fun_add_spec in MMT0.
        destruct (TState.mid ts ++ [lab] == TState.mid ts ++ [lab]); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss. lia.
      }
      inv RTC0; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      rewrite app_nil_r in *. subst. esplits; eauto.
      { apply trace_refine_eq. }
      { i. splits; ss. apply refine_empty; ss. }
      i. splits; ss. rewrite fun_add_spec in MMT0.
      destruct (TState.mid ts ++ [lab] == TState.mid ts ++ [lab]); cycle 1.
      { exfalso. apply c. ss. }
      inv MMT0. ss.
    + inv RTC; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      inv ONE0. inv NORMAL_STEP; inv STEP; ss; inv STMT; rewrite MMT in MMT0; inv MMT0; try lia.
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
      hexploit chkpt_fn_cases; [apply RTC | | left |]; ss; eauto.
      { rewrite app_nil_l. eauto. }
      i. des; hexploit read_only_statements; eauto; i; des; subst; ss.
      * destruct thr_term'. esplits; eauto.
        { hexploit trace_refine_app; [apply trace_refine_eq | apply H | rewrite app_nil_l; eauto]. }
        unfold STOP. i. des; try by destruct c_pfx; ss.
        rewrite Cont.loops_app_distr in *. des. inv RETURN1. ss.
      * inv CALL_DONE2. inv ONE; inv NORMAL_STEP; inv STEP; ss; inv STMT; cycle 1.
        { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
          { ii. inv H0. ss. }
          { ii. inv H0. ss. }
          i. ss.
        }
        hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
        { ii. inv H0. ss. }
        { ii. inv H0. ss. }
        i. inv H0. rewrite app_nil_r in *. subst.
        rewrite snoc_eq_snoc in CONT. des. subst.
        hexploit stop_means_no_step; eauto; ss.
        { unfold STOP. left. ss. }
        i. des. inv H0. rewrite app_nil_r in *.
        inv ONE0. inv NORMAL_STEP; inv STEP; inv STMT; ss.
        { hexploit Thread.step_time_mon; try exact CALL_DONE0; eauto. i. ss.
          rewrite fun_add_spec in *. destruct (TState.mid ts ++ [lab] == TState.mid ts ++ [lab]); cycle 1.
          { exfalso. apply c. ss. }
          inv MMT0. ss. lia.
        }
        inv RTC0; ss; cycle 1.
        { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
        rewrite fun_add_spec in *. destruct (TState.mid ts ++ [lab] == TState.mid ts ++ [lab]); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss.
        esplits; eauto.
        { rewrite app_nil_r. apply trace_refine_eq. }
        i. splits; ss. apply trace_refine_eq.
    + inv RTC; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      inv ONE0. inv NORMAL_STEP; inv STEP; inv STMT; ss; rewrite MMT in MMT0; inv MMT0; try lia.
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
    hexploit chkpt_fn_cases; [apply RTC | | |]; eauto.
    { rewrite app_nil_l. ss. }
    hexploit chkpt_fn_cases; [apply RTC0 | | |]; eauto.
    { rewrite app_nil_l. ss. }
    i. des; ss.
    + (* (ONGOING, ONGOING) *)
      destruct thr_term. destruct thr_term'. ss. subst.
      hexploit IHF; eauto. ss. i. des.
      hexploit lift_cont; eauto. ss.
      intros TR_X. eapply rtc_relax_base_cont in TR_X; try rewrite app_nil_r; ss.
      esplits; [| eauto | |].
      * econs 2; eauto; cycle 1.
        { rewrite app_nil_l. ss. }
        econs; eauto. rewrite app_nil_r. ss.
      * unfold STOP. i. des; try by destruct c_pfx; ss.
        rewrite Cont.loops_app_distr in *. des. inv RETURN1. ss.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx0; ss.
        rewrite Cont.loops_app_distr in *. des. inv RETURN1. ss.
    + (* (ONGOING, DONE) *)
      hexploit CALL_DONE3; ss. i. clear CALL_DONE3.
      destruct thr_term. destruct thr_term'. ss. subst.
      hexploit IHF; eauto. ss. i. des.
      inv CALL_DONE2. inv ONE; inv NORMAL_STEP0; inv STEP; ss; inv STMT.
      { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
        { ii. inv H0. ss. }
        { ii. inv H0. ss. }
        i. ss.
      }
      hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H0. ss. }
      { ii. inv H0. ss. }
      i. inv H0. rewrite app_nil_r in *. subst.
      rewrite snoc_eq_snoc in CONT. des. subst.
      hexploit stop_means_no_step; eauto; ss.
      { unfold STOP. left. ss. }
      i. des. inv H0. rewrite app_nil_r in *.
      hexploit STOP_SND.
      { unfold STOP. repeat right. esplits; ss. }
      i. des. subst.
      esplits; eauto.
      * econs 2; cycle 2.
        { rewrite app_nil_l. ss. }
        { econs; eauto. ss. rewrite app_nil_r. ss. }
        hexploit lift_cont; try exact TRACE; eauto. ss.
        intros TR_X. eapply rtc_relax_base_cont in TR_X; try rewrite app_nil_r; ss.
        rewrite <- (app_nil_r tr_x). eapply Thread.rtc_trans; eauto.
        econs 2; eauto; try rewrite app_nil_r; ss.
        econs; try rewrite app_nil_r; ss. try by econs; econs; eauto.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx; ss.
        rewrite Cont.loops_app_distr in *. des. inv RETURN1. ss.
    + (* (DONE, ONGOING) *)
      inv CALL_DONE2. inv ONE; inv NORMAL_STEP0; inv STEP; ss; inv STMT.
      { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
        { ii. inv H. ss. }
        { ii. inv H. ss. }
        i. ss.
      }
      hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H. ss. }
      { ii. inv H. ss. }
      i. inv H. rewrite app_nil_r in *. subst.
      rewrite snoc_eq_snoc in CONT. des. subst.
      hexploit stop_means_no_step; eauto; ss.
      { unfold STOP. left. ss. }
      i. des. inv H0. ss. rewrite app_nil_r in *.
      hexploit IHF; eauto. ss. i. des.
      hexploit STOP_FST.
      { unfold STOP. repeat right. esplits; ss. }
      i. des. subst.
      esplits; eauto.
      * hexploit trace_refine_app; [apply H3 | |]; cycle 1.
        { rewrite app_nil_r. eauto. }
        apply trace_refine_eq.
      * destruct thr_term'. ss. subst.
        unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx; ss.
        rewrite Cont.loops_app_distr in *. des. inv RETURN1. ss.
    + (* (DONE, DONE) *)
      inv CALL_DONE7. inv ONE; inv NORMAL_STEP0; inv STEP; ss; inv STMT.
      { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
        { ii. inv H. ss. }
        { ii. inv H. ss. }
        i. ss.
      }
      hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H. ss. }
      { ii. inv H. ss. }
      i. inv H. rewrite app_nil_r in *. subst.
      rewrite snoc_eq_snoc in CONT. des. subst.
      hexploit stop_means_no_step; eauto; ss.
      { unfold STOP. left. ss. }
      i. des. inv H0. rewrite app_nil_r in *.

      inv CALL_DONE2. inv ONE; inv NORMAL_STEP0; inv STEP; ss; inv STMT.
      { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
        { ii. inv H. ss. }
        { ii. inv H. ss. }
        i. ss.
      }
      hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H. ss. }
      { ii. inv H. ss. }
      i. inv H. rewrite app_nil_r in *. subst.
      rewrite snoc_eq_snoc in CONT. des. subst.
      hexploit stop_means_no_step; eauto; ss.
      { unfold STOP. left. ss. }
      i. des. inv H0. rewrite app_nil_r in *.

      hexploit IHF; eauto. ss. i. des.
      hexploit STOP_FST.
      { unfold STOP. repeat right. esplits; ss. }
      hexploit STOP_SND.
      { unfold STOP. repeat right. esplits; ss. }
      i. des. subst.
      inv H0.
      esplits; eauto.
      hexploit trace_refine_app; [apply H4 | |]; cycle 1.
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
    destruct (EquivDec.equiv_dec (sem_expr (TState.regs ts) e) (Val.bool true)).
    + hexploit IHENVTJ1; [| apply RTC | apply RTC0 |]; ss.
      i. des. eexists tr_x. eexists s_x. eexists c_x. eexists ts_x. splits; ss.
      econs 2; eauto; [econs; eauto |]; rewrite app_nil_l; ss.
    + hexploit IHENVTJ2; [| apply RTC | apply RTC0 |]; ss.
      i. des. eexists tr_x. eexists s_x. eexists c_x. eexists ts_x. splits; ss.
      econs 2; eauto; [econs; eauto |]; rewrite app_nil_l; ss.
  - subst.
    hexploit seq_cases; try exact EX2; eauto. hexploit seq_cases; try exact EX1; eauto. i. des; subst.
    + (* seq-left-ongoing, seq-left-ongoing *)
      hexploit IHENVTJ1; eauto. unfold DR. intros X. hexploit X; try exact SEQ_LEFT_ONGOING2; eauto. i. des. ss.
      hexploit lift_stmt; eauto. s. instantiate (1 := s_r). i. des. subst.
      unfold seq_sc, seq_sc_unzip in H1. ss. rewrite pair_equal_spec in *. des. subst.
      esplits; eauto.
      * assert (STOP s_m0 c_m0 \/ ~ STOP s_m0 c_m0); [apply classic |]. des.
        -- generalize H0. intros STOP. apply STOP_FST in STOP. des. subst. i.
           rewrite <- H2 in *. rewrite pair_equal_spec in *. des. subst. split; ss.
        -- i. exfalso.
           symmetry in SEQ_LEFT_ONGOING3. hexploit seq_sc_stop; try exact SEQ_LEFT_ONGOING3; eauto. i.
           apply H3 in H1. ss.
      * assert (STOP s_m c_m \/ ~ STOP s_m c_m); [apply classic |]. des.
        -- generalize H0. intros STOP. apply STOP_SND in STOP. des. subst. i.
           rewrite <- H2 in *. rewrite pair_equal_spec in *. des. subst. split; ss.
        -- i. exfalso.
           symmetry in SEQ_LEFT_ONGOING3. hexploit seq_sc_stop; try exact SEQ_LEFT_ONGOING0; eauto. i.
           apply H3 in H1. ss.
    + (* seq-left-done, seq-left-ongoing *)
      hexploit lift_mmt; try exact SEQ_LEFT_DONE0; eauto. i.
      hexploit lift_mmt; try exact SEQ_LEFT_DONE1; eauto. i.
      hexploit lift_mmt; try exact SEQ_LEFT_ONGOING; eauto. i.
      des. ss.

      hexploit mid_flat_eq; try exact SEQ_LEFT_DONE0; ss; ss. intro MID_FLAT_EQ. rewrite <- MID_FLAT_EQ in *.

      assert (MMTS_PROJ_EQ: mmts0 |₁ mmt_id_exp (TState.mid ts) labs_l = Thread.mmts thr_term |₁ mmt_id_exp (TState.mid ts) labs_l).
      { eapply Mmts.proj_disj_eq; eauto. apply exp_disj_pres. econs. ii. inv DISJ. eapply H0. inv H. econs; eauto. }

      rewrite <- MMTS_PROJ_EQ in *. hexploit IHENVTJ1; eauto. unfold DR. intros X. hexploit X; try exact UNLIFT1; eauto. i. des. ss.
      hexploit STOP_FST.
      { unfold STOP. left. ss. }
      i. des. subst.

      hexploit Mmts.proj_compl_eq; [| exact COMPL_EQ |]; eauto.
      { rewrite H2 in *. ss. }
      intros MMTS_EQ. rewrite <- MMTS_EQ in *. rewrite <- MMTS_PROJ_EQ in TRACE.

      hexploit lift_mmt; try exact TRACE; eauto. i. des. ss.
      specialize LIFT2 with mmts. repeat rewrite <- Mmts.proj_idemp in LIFT2. rewrite Mmts.proj_compl_union in LIFT2.
      rewrite COMPL_EQ1 in LIFT2. rewrite Mmts.proj_compl_union in LIFT2.

      destruct thr_term. ss. esplits; eauto.
      { hexploit trace_refine_app; [exact H3| |]; cycle 1.
        { rewrite app_nil_r. eauto. }
        apply trace_refine_eq.
      }

      (* STOP contradiction *)
      cut (STOP s_m c_m -> False).
      { i. unguard. hexploit seq_sc_stop; eauto. intuition. }

      intro CONTRA. apply STOP_SND in CONTRA. des. subst. unguard. des; ss.
    + (* seq-left-ongoing, seq-left-done *)
      hexploit IHENVTJ1; eauto. unfold DR. intros X. hexploit X; try exact SEQ_LEFT_ONGOING; eauto. i. des. ss.
      hexploit STOP_SND.
      { unfold STOP. left. ss. }
      i. des. subst.

      hexploit lift_stmt; eauto. s. instantiate (1 := s_r). i. des.
      unfold seq_sc, seq_sc_unzip in *. ss. apply pair_equal_spec in H1, H2. des. subst.
      destruct thr_term'. ss. esplits; try eapply Thread.rtc_trans; eauto.
      { rewrite app_assoc. apply trace_refine_app; ss. apply trace_refine_eq. }

      (* STOP contradiction *)
      cut (STOP s_m c_m -> False).
      { i. unguard. hexploit seq_sc_stop; eauto. intuition. }

      intro CONTRA. apply STOP_FST in CONTRA. des. subst. unguard. des; ss.
    + (* seq-left-done, seq-left-done *)
      hexploit lift_mmt; try exact SEQ_LEFT_DONE3; eauto.
      hexploit lift_mmt; try exact SEQ_LEFT_DONE4; eauto.
      hexploit lift_mmt; try exact SEQ_LEFT_DONE0; eauto.
      hexploit lift_mmt; try exact SEQ_LEFT_DONE1; eauto.
      i. des. ss.

      hexploit mid_flat_eq; try exact SEQ_LEFT_DONE3; ss; ss. intro MID_FLAT_EQ. rewrite <- MID_FLAT_EQ in *.

      assert (MMTS_PROJ_EQ: mmts1 |₁ mmt_id_exp (TState.mid ts) labs_l = Thread.mmts thr_term |₁ mmt_id_exp (TState.mid ts) labs_l).
      { eapply Mmts.proj_disj_eq; eauto. apply exp_disj_pres. econs. ii. inv DISJ. eapply H0. inv H. econs; eauto. }
      rewrite <- MMTS_PROJ_EQ in *. hexploit IHENVTJ1; eauto. unfold DR. intros X. hexploit X; try exact UNLIFT2; eauto. s. i. des. ss.
      hexploit STOP_FST.
      { unfold STOP. left. ss. }
      i. des. subst.
      hexploit STOP_SND.
      { unfold STOP. left. ss. }
      i. des. subst.

      hexploit Mmts.proj_compl_eq; [| exact COMPL_EQ1 |]; eauto.
      { rewrite H2 in *. ss. }
      intros MMTS_EQ. rewrite <- MMTS_EQ in *. rewrite <- MMTS_PROJ_EQ in TRACE.

      hexploit IHENVTJ2; eauto. unfold DR. intros Y. hexploit Y; try exact SEQ_LEFT_DONE4; eauto. i. des. ss.

      hexploit lift_stmt; try exact SEQ_LEFT_DONE3; eauto. s. instantiate (1 := s_r). i. des.
      unfold seq_sc, seq_sc_unzip in *. ss. apply pair_equal_spec in H5, H6. des. subst.
      destruct thr_term'. ss. esplits; try eapply Thread.rtc_trans; eauto.
      { rewrite <- app_assoc. apply trace_refine_app; try apply trace_refine_eq. apply trace_refine_nil_ins; ss. }
      intros STOP. apply STOP_FST0 in STOP. des. splits; ss.
      rewrite <- (app_nil_l []). apply trace_refine_app; ss.
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
    inv RTC0. ss.
    { destruct thr_term. ss. esplits; eauto.
      { rewrite app_nil_r. apply trace_refine_eq. }
      { i. splits; ss. apply trace_refine_eq. }
      unfold STOP. i. des; ss.
    }
    apply IHENVTJ in FNJ. unfold DR in FNJ. rename FNJ into IH.
    hexploit loop_cases; [apply RTC | | |]; eauto.
    { rewrite app_nil_l. ss. }
    i. des; cycle 1.
    + (* EX1: LOOP-DONE *)
      hexploit stop_means_no_step; eauto.
      { econs; eauto. }
      i. des. destruct thr_term. inv H. ss.
      hexploit last_loop_iter; eauto; ss.
      { rewrite app_nil_l. ss. }
      i. des. subst. rename H0 into TR3.
      symmetry in H1. rewrite <- app_nil_l in H1. apply snoc_eq_snoc in H1. des. subst. cleartriv.

      assert (
        s1 = stmt_chkpt r [stmt_return r] lab :: s_body
        /\ c1 = []
        /\ ts.(TState.time) <= ts1.(TState.time)
        /\ ts.(TState.mid) = ts1.(TState.mid)
      ).
      { unguard. des; splits; subst; ss.
        { hexploit Thread.step_time_mon; [exact LAST_CONT |]; eauto. }
        hexploit mid_flat_eq; try exact LAST_CONT; ss; ss.
      }

      des. subst. rewrite H3 in *.
      inv H2; try inv THR. inv ONE0. inv NORMAL_STEP0; inv STEP; ss; inv STMT.
      * (* EX1: CHKPT-CALL *)
        inv RTC0; try inv THR.

        (* EX1: chkpt return *)
        inv ONE0. inv NORMAL_STEP0; inv STEP; ss; inv STMT; ss; cycle 1.
        { rewrite app_nil_r in CONT. destruct c_loops; ss. inv CONT. destruct c_loops; ss. }
        rewrite app_nil_r in CONT. destruct c_loops; ss; inv CONT; cycle 1.
        { destruct c_loops; ss. }

        hexploit lift_mmt; eauto. ss. i. des.
        eapply equal_f in COMPL_EQ. revert COMPL_EQ. instantiate (1 := TState.mid ts1 ++ [lab0]). i.

        assert (COMPL_IN: Ensembles.In (list Label) (Complement (list Label) (mmt_id_exp (TState.mid ts1) labs')) (TState.mid ts1 ++ [lab0])).
        { clear - NIN.
          unfold Ensembles.In. unfold Complement. ii.
          inv H. apply app_inv_head in MID. inv MID. ss.
        }

        symmetry in COMPL_EQ.
        hexploit Mmts.proj_inv; eauto.
        unfold Mmts.proj. ss. condtac; ss.
        funtac. intro MID_MMT.

        (* EX2: chkpt replay *)
        inv ONE; inv NORMAL_STEP0; inv STEP; inv STMT; ss; rewrite MID_MMT in MMT0; inv MMT0; ss.
        { lia. }

        assert (TS_EQ: VRegMap.add r0 (VRegMap.find r0 (TState.regs ts1)) (TState.regs ts) =
                       VRegMap.add r0 (VRegMap.find r0 (TState.regs ts1)) (TState.regs ts1)).
        { move TR3 at bottom. unguard. des; ss; [rewrite LAST_FIRST1 | rewrite LAST_CONT2]; ss; rewrite VRegMap.add_add; ss. }

        move RTC1 at bottom. rewrite VRegMap.add_add in *.
        hexploit loop_cases; [apply RTC1 | | |]; eauto.
        { rewrite app_nil_l. ss. }
        i. rewrite TS_EQ in *. des; ss; cycle 1.
        -- (* EX2: LOOP-DONE *)
          hexploit stop_means_no_step; eauto.
          { econs; eauto. }
          i. des. destruct thr_term'. inv H. ss.
          hexploit first_loop_iter; eauto.
          { rewrite app_nil_l. ss. }
          i. des; ss; cycle 1.
          ++ (* EX2: FIRST-DONE *)
            hexploit IH; [exact RTC2 | |]; eauto; ss. i. des.
            hexploit STOP_FST.
            { unfold STOP. right. left. esplits; ss. }
            hexploit STOP_SND.
            { unfold STOP. right. right. left. esplits; ss. }
            i. des. subst. ss.
          ++ (* EX2: FIRST-ONGOING *)
            symmetry in FIRST_ONGOING. rewrite <- app_nil_l in FIRST_ONGOING.
            apply snoc_eq_snoc in FIRST_ONGOING. des. subst. cleartriv.
            hexploit IH; [exact RTC2 | |]; eauto; ss. i. des.
            hexploit STOP_FST.
            { unfold STOP. right. left. esplits; ss. }
            hexploit STOP_SND.
            { unfold STOP. right. left. esplits; ss. }
            i. des. subst. inv H0.
            esplits; eauto; cycle 1.
            { rewrite app_nil_r. ss. }
            hexploit trace_refine_app; [exact H6| | ]; ss; cycle 1.
            { repeat rewrite app_nil_r. eauto. }
            apply trace_refine_eq.
        -- (* EX2: LOOP-ONGOING *)
          hexploit first_loop_iter; eauto.
          { rewrite app_nil_l. ss. }
          i. des; ss; cycle 1.
          ++ (* EX2: FIRST-DONE *)
            hexploit IH; [exact RTC2 | |]; eauto; ss. i. des.
            hexploit STOP_FST.
            { unfold STOP. right. left. esplits; ss. }
            hexploit STOP_SND.
            { unfold STOP. right. right. left. esplits; ss. }
            i. des. subst. ss.
          ++ (* EX2: FIRST-ONGOING *)
            hexploit IH; [exact RTC2 | |]; eauto; ss. i. des.
            hexploit STOP_FST.
            { unfold STOP. right. left. esplits; ss. }
            i. des. subst.
            destruct thr_term'; ss. subst.
            esplits; eauto.
            { hexploit trace_refine_app; [exact H5| | ]; ss; cycle 1.
              { rewrite app_nil_r. eauto. }
              apply trace_refine_eq.
            }
            unfold STOP. i. des; try by destruct c_pfx; ss.
            inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
            hexploit STOP_SND.
            { unfold STOP. repeat right. esplits; ss. }
            i. des. ss.
      * (* EX1: CHKPT-REPLAY *)
        hexploit lift_mmt; eauto. ss. i. des.
        eapply equal_f in COMPL_EQ. revert COMPL_EQ. instantiate (1 := TState.mid ts1 ++ [lab0]). i.
        assert (COMPL_IN: Ensembles.In (list Label) (Complement (list Label) (mmt_id_exp (TState.mid ts1) labs')) (TState.mid ts1 ++ [lab0])).
        { clear - NIN.
          unfold Ensembles.In. unfold Complement. ii.
          inv H. apply app_inv_head in MID. inv MID. ss.
        }
        symmetry in COMPL_EQ.
        hexploit Mmts.proj_inv; eauto.
        unfold Mmts.proj. ss. condtac; ss.
        funtac. intro MID_MMT.

        inv ONE; inv NORMAL_STEP0; inv STEP; inv STMT; ss; rewrite MID_MMT in MMT0; rewrite MMT in MMT0; inv MMT0; ss.
        { lia. }

        assert (TS_EQ: VRegMap.add r (Mmt.val mmt0) (TState.regs ts) =
                       VRegMap.add r (Mmt.val mmt0) (TState.regs ts1)).
        { move TR3 at bottom. unguard. des; ss; [rewrite LAST_FIRST1 | rewrite LAST_CONT2]; ss; rewrite VRegMap.add_add; ss. }

        move RTC1 at bottom. rewrite VRegMap.add_add in *.
        hexploit loop_cases; [apply RTC1 | | |]; eauto.
        { rewrite app_nil_l. ss. }
        i. rewrite TS_EQ in *. des; ss; cycle 1.
        -- (* EX2: LOOP-DONE *)
          hexploit stop_means_no_step; eauto.
          { econs; eauto. }
          i. des. destruct thr_term'. inv H. ss.
          hexploit first_loop_iter; eauto.
          { rewrite app_nil_l. ss. }
          i. des; ss; cycle 1.
          ++ (* EX2: FIRST-DONE *)
            hexploit IH; [exact RTC0 | |]; eauto; ss. i. des.
            hexploit STOP_FST.
            { unfold STOP. right. left. esplits; ss. }
            hexploit STOP_SND.
            { unfold STOP. right. right. left. esplits; ss. }
            i. des. subst. ss.
          ++ (* EX2: FIRST-ONGOING *)
            symmetry in FIRST_ONGOING. rewrite <- app_nil_l in FIRST_ONGOING.
            apply snoc_eq_snoc in FIRST_ONGOING. des. subst. cleartriv.
            hexploit IH; [exact RTC0 | |]; eauto; ss. i. des.
            hexploit STOP_FST.
            { unfold STOP. right. left. esplits; ss. }
            hexploit STOP_SND.
            { unfold STOP. right. left. esplits; ss. }
            i. des. subst. inv H0.
            esplits; eauto; cycle 1.
            { rewrite app_nil_r. ss. }
            hexploit trace_refine_app; [exact H6| | ]; ss; cycle 1.
            { repeat rewrite app_nil_r. eauto. }
            apply trace_refine_eq.
        -- (* EX2: LOOP-ONGOING *)
          hexploit first_loop_iter; eauto.
          { rewrite app_nil_l. ss. }
          i. des; ss; cycle 1.
          ++ (* EX2: FIRST-DONE *)
            hexploit IH; [exact RTC0 | |]; eauto; ss. i. des.
            hexploit STOP_FST.
            { unfold STOP. right. left. esplits; ss. }
            hexploit STOP_SND.
            { unfold STOP. right. right. left. esplits; ss. }
            i. des. subst. ss.
          ++ (* EX2: FIRST-ONGOING *)
            hexploit IH; [exact RTC0 | |]; eauto; ss. i. des.
            hexploit STOP_FST.
            { unfold STOP. right. left. esplits; ss. }
            i. des. subst.
            destruct thr_term'. ss. subst.
            esplits; eauto.
            { hexploit trace_refine_app; [exact H5| | ]; ss; cycle 1.
              { rewrite app_nil_r. eauto. }
              apply trace_refine_eq.
            }
            unfold STOP. i. des; try by destruct c_pfx; ss.
            inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
            hexploit STOP_SND.
            { unfold STOP. repeat right. esplits; ss. }
            i. des. ss.
    + (* EX1: LOOP-ONGOING *)
      hexploit last_loop_iter; eauto; ss.
      { rewrite app_nil_l. ss. }
      i. des. rename H0 into TR3.

      assert (
        s1 = stmt_chkpt r [stmt_return r] lab :: s_body
        /\ c1 = []
        /\ ts.(TState.time) <= ts1.(TState.time)
        /\ ts.(TState.mid) = ts1.(TState.mid)
      ).
      { unguard. des; splits; subst; ss.
        { hexploit Thread.step_time_mon; [exact LAST_CONT |]; eauto. }
        hexploit mid_flat_eq; try exact LAST_CONT; ss; ss.
      }
      des. subst. rewrite H5 in *.

      inv H2.
      { (* LAST SECOND ITER *)
        admit.
      }

      inversion ONE0. inv NORMAL_STEP0; inv STEP; ss; inv STMT.
      * (* EX1: CHKPT-CALL *)
        inv RTC0.
        { (* LAST SECOND ITER *)
          admit.
        }
        inversion ONE1. inv NORMAL_STEP0; inv STEP; ss; inv STMT; ss; cycle 1.
        { rewrite app_nil_r in CONT. destruct c_loops; ss. inv CONT. destruct c_loops; ss. }
        rewrite app_nil_r in CONT. destruct c_loops; ss; inv CONT; cycle 1.
        { destruct c_loops; ss. }
        hexploit lift_mmt; eauto. ss. i. des.
        eapply equal_f in COMPL_EQ. revert COMPL_EQ. instantiate (1 := (TState.mid ts1 ++ [lab0])). i.

        assert (COMPL_IN: Ensembles.In (list Label) (Complement (list Label) (mmt_id_exp (TState.mid ts1) labs')) (TState.mid ts1 ++ [lab0])).
        { clear - NIN.
          unfold Ensembles.In. unfold Complement. ii.
          inv H. apply app_inv_head in MID. inv MID. ss.
        }
        symmetry in COMPL_EQ.
        hexploit Mmts.proj_inv; eauto. ss.
        unfold Mmts.proj. ss. condtac; ss.
        funtac. intro MID_MMT.

        inv ONE; inv NORMAL_STEP0; inv STEP; inv STMT; ss; rewrite MID_MMT in MMT0; inv MMT0; ss.
        { lia. }

        assert (TS_EQ: VRegMap.add r0 (VRegMap.find r0 (TState.regs ts1)) (TState.regs ts) =
                       VRegMap.add r0 (VRegMap.find r0 (TState.regs ts1)) (TState.regs ts1)).
        { move TR3 at bottom. unguard. des; ss; [rewrite LAST_FIRST1 | rewrite LAST_CONT2]; ss; rewrite VRegMap.add_add; ss. }

        move RTC1 at bottom. rewrite VRegMap.add_add in *.
        hexploit loop_cases; [apply RTC1 | | |]; eauto.
        { rewrite app_nil_l. ss. }
        i. rewrite TS_EQ in *. des; ss; cycle 1.
        -- (* EX2: LOOP-DONE *)
          hexploit stop_means_no_step; eauto.
          { econs; eauto. }
          i. des. destruct thr_term'. inv H. ss.
          hexploit first_loop_iter; eauto.
          { rewrite app_nil_l. ss. }
          i. des; ss; cycle 1.
          ++ (* EX2: FIRST-DONE *)
            hexploit IH; [exact RTC2 | |]; eauto; ss. i. des.
            hexploit STOP_SND.
            { unfold STOP. right. right. left. esplits; ss. }
            i. des. subst.
            destruct thr_term. ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r0
                   (stmt_chkpt r0 [stmt_return r0] lab :: s) []]).
            intro TR_X. eapply rtc_relax_base_cont in TR_X; eauto.

            eexists (tr3 ++ tr_x ++ tr2).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; [| apply trace_refine_eq].
              rewrite app_nil_r. rewrite app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              rewrite <- (app_nil_r tr2). eapply rtc_relax_base_cont in FIRST_DONE1; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; (try by econs; eauto); cycle 1.
              { rewrite app_nil_l. ss. }
              econs; [| rewrite app_nil_l]; ss. econs 13. econs; ss.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; try rewrite LAST_FIRST1 in *; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 7. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 8. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss. econs; eauto.
            ** rewrite <- (app_nil_r tr3). eapply rtc_relax_base_cont in LAST_CONT; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 12. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 7. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 8. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss. econs; eauto.
          ++ (* EX2: FIRST-ONGOING *)
            symmetry in FIRST_ONGOING. rewrite <- app_nil_l in FIRST_ONGOING.
            apply snoc_eq_snoc in FIRST_ONGOING. des. subst. cleartriv.
            hexploit IH; [exact RTC2 | |]; eauto; ss. i. des.
            hexploit STOP_SND.
            { unfold STOP. right. left. esplits; ss. }
            i. des. subst.

            destruct thr_term. ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r0
                   (stmt_chkpt r0 [stmt_return r0] lab :: s) []]).
            intro TR_X. eapply rtc_relax_base_cont in TR_X; eauto.

            eexists (tr3 ++ tr_x ++ []).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; eauto; [|apply trace_refine_eq].
              repeat rewrite app_nil_r. eauto.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              econs 2; (try by econs; eauto); cycle 1.
              { rewrite app_nil_l. ss. }
              econs; [| rewrite app_nil_l]; ss. econs 13. econs; ss.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; try rewrite LAST_FIRST1 in *; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 7. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 8. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss. econs; eauto.
            ** rewrite <- (app_nil_r tr3). eapply rtc_relax_base_cont in LAST_CONT; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 12. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 7. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 8. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss. econs; eauto.
        -- (* EX2: LOOP-ONGOING *)
          hexploit first_loop_iter; eauto.
          { rewrite app_nil_l. ss. }
          i. des; ss; cycle 1.
          ++ (* EX2: FIRST-DONE *)
            hexploit IH; [exact RTC2 | |]; eauto; ss. i. des.
            hexploit STOP_SND.
            { unfold STOP. right. right. left. esplits; ss. }
            i. des. subst.
            destruct thr_term, thr_term'; ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r0
                   (stmt_chkpt r0 [stmt_return r0] lab :: s) []]).
            intro TR_X. eapply rtc_relax_base_cont in TR_X; eauto.

            eexists (tr3 ++ tr_x ++ tr2).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; [| apply trace_refine_eq].
              rewrite app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              eapply rtc_relax_base_cont in FIRST_DONE1; eauto.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; try rewrite LAST_FIRST1 in *; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 7. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 8. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss. econs; eauto.
            ** rewrite <- (app_nil_r tr3). eapply rtc_relax_base_cont in LAST_CONT; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 12. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 7. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 8. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss. econs; eauto.
          ++ (* EX2: FIRST-ONGOING *)
            hexploit IH; [exact RTC2 | |]; eauto; ss. i. des.
            i. des. subst.

            destruct thr_term, thr_term'; ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r0
                   (stmt_chkpt r0 [stmt_return r0] lab :: s) []]).
            intro TR_X. eapply rtc_relax_base_cont in TR_X; eauto.

            eexists (tr3 ++ tr_x). eexists s_x.
            eexists (c_x ++ [Cont.loopcont (TState.regs ts) r0 (stmt_chkpt r0 [stmt_return r0] lab :: s) []]).
            eexists ts_x.
            splits; ss; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq. }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. subst. ss.
            }
            { unfold STOP. i. des; try by destruct c_pfx; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_SND.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. subst. ss.
            }
            eapply Thread.rtc_trans; eauto.
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; try rewrite LAST_FIRST1 in *; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 7. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 8. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss. econs; eauto.
            ** rewrite <- (app_nil_r tr3). eapply rtc_relax_base_cont in LAST_CONT; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 12. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 7. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 8. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss. econs; eauto.
      * (* EX1: CHKPT-REPLAY *)
        rewrite app_nil_r in *. subst.
        hexploit lift_mmt; eauto. ss. i. des.
        eapply equal_f in COMPL_EQ. revert COMPL_EQ. instantiate (1 := TState.mid ts1 ++ [lab0]). i.
        assert (COMPL_IN: Ensembles.In (list Label) (Complement (list Label) (mmt_id_exp (TState.mid ts1) labs')) (TState.mid ts1 ++ [lab0])).
        { clear - NIN.
          unfold Ensembles.In. unfold Complement. ii.
          inv H. apply app_inv_head in MID. inv MID. ss.
        }
        symmetry in COMPL_EQ.
        hexploit Mmts.proj_inv; eauto.
        unfold Mmts.proj. ss. condtac; ss.
        funtac. intro MID_MMT.
        inv ONE; inv NORMAL_STEP0; inv STEP; inv STMT; ss; rewrite MID_MMT in MMT0; rewrite MMT in MMT0; inv MMT0; ss.
        { lia. }

        assert (TS_EQ: VRegMap.add r (Mmt.val mmt0) (TState.regs ts) =
                       VRegMap.add r (Mmt.val mmt0) (TState.regs ts1)).
        { move TR3 at bottom. unguard. des; ss; [rewrite LAST_FIRST1 | rewrite LAST_CONT2]; ss; rewrite VRegMap.add_add; ss. }

        move RTC1 at bottom. rewrite VRegMap.add_add in *.
        hexploit loop_cases; [apply RTC1 | | |]; eauto.
        { rewrite app_nil_l. ss. }
        i. rewrite TS_EQ in *. des; ss; cycle 1.
        -- (* EX2: LOOP-DONE *)
          hexploit stop_means_no_step; eauto.
          { econs; eauto. }
          i. des. destruct thr_term'. inv H. ss.
          hexploit first_loop_iter; eauto.
          { rewrite app_nil_l. ss. }
          i. des; ss; cycle 1.
          ++ (* EX2: FIRST-DONE *)
            hexploit IH; [exact RTC0 | |]; eauto; ss. i. des.
            hexploit STOP_SND.
            { unfold STOP. right. right. left. esplits; ss. }
            i. des. subst.
            destruct thr_term. ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r
                   (stmt_chkpt r [stmt_return r] lab :: s0) []]).
            intro TR_X. eapply rtc_relax_base_cont in TR_X; eauto.

            eexists (tr3 ++ tr_x ++ tr2).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; [| apply trace_refine_eq].
              rewrite app_nil_r. rewrite app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              rewrite <- (app_nil_r tr2). eapply rtc_relax_base_cont in FIRST_DONE1; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; (try by econs; eauto); cycle 1.
              { rewrite app_nil_l. ss. }
              econs; [| rewrite app_nil_l]; ss. econs 13. econs; ss.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; try rewrite LAST_FIRST1 in *; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              ss. rewrite VRegMap.add_add. econs; eauto.
            ** rewrite <- (app_nil_r tr3). eapply rtc_relax_base_cont in LAST_CONT; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 12. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              ss. rewrite VRegMap.add_add. econs; eauto.
          ++ (* EX2: FIRST-ONGOING *)
            symmetry in FIRST_ONGOING. rewrite <- app_nil_l in FIRST_ONGOING.
            apply snoc_eq_snoc in FIRST_ONGOING. des. subst. cleartriv.
            hexploit IH; [exact RTC0 | |]; eauto; ss. i. des.
            hexploit STOP_SND.
            { unfold STOP. right. left. esplits; ss. }
            i. des. subst.

            destruct thr_term. ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r
                   (stmt_chkpt r [stmt_return r] lab :: s0) []]).
            intro TR_X. eapply rtc_relax_base_cont in TR_X; eauto.

            eexists (tr3 ++ tr_x ++ []).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; eauto; [|apply trace_refine_eq].
              repeat rewrite app_nil_r. eauto.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              econs 2; (try by econs; eauto); cycle 1.
              { rewrite app_nil_l. ss. }
              econs; [| rewrite app_nil_l]; ss. econs 13. econs; ss.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; try rewrite LAST_FIRST1 in *; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              rewrite VRegMap.add_add. econs; eauto.
            ** rewrite <- (app_nil_r tr3). eapply rtc_relax_base_cont in LAST_CONT; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 12. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              rewrite VRegMap.add_add. econs; eauto.
        -- (* EX2: LOOP-ONGOING *)
          hexploit first_loop_iter; eauto.
          { rewrite app_nil_l. ss. }
          i. des; ss; cycle 1.
          ++ (* EX2: FIRST-DONE *)
            hexploit IH; [exact RTC0 | |]; eauto; ss. i. des.
            hexploit STOP_SND.
            { unfold STOP. right. right. left. esplits; ss. }
            i. des. subst.
            destruct thr_term, thr_term'; ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r
                   (stmt_chkpt r [stmt_return r] lab :: s0) []]).
            intro TR_X. eapply rtc_relax_base_cont in TR_X; eauto.

            eexists (tr3 ++ tr_x ++ tr2).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; [| apply trace_refine_eq].
              rewrite app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              eapply rtc_relax_base_cont in FIRST_DONE1; eauto.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; try rewrite LAST_FIRST1 in *; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              rewrite VRegMap.add_add. econs; eauto.
            ** rewrite <- (app_nil_r tr3). eapply rtc_relax_base_cont in LAST_CONT; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 12. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              rewrite VRegMap.add_add. econs; eauto.
          ++ (* EX2: FIRST-ONGOING *)
            hexploit IH; [exact RTC0 | |]; eauto; ss. i. des.
            i. des. subst.

            destruct thr_term, thr_term'; ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r
                   (stmt_chkpt r [stmt_return r] lab :: s0) []]).
            intro TR_X. eapply rtc_relax_base_cont in TR_X; eauto.

            eexists (tr3 ++ tr_x). eexists s_x.
            eexists (c_x ++ [Cont.loopcont (TState.regs ts) r (stmt_chkpt r [stmt_return r] lab :: s0) []]).
            eexists ts_x.
            splits; ss; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq. }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. subst. ss.
            }
            { unfold STOP. i. des; try by destruct c_pfx; ss.
              inv RETURN. rewrite Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_SND.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. subst. ss.
            }
            eapply Thread.rtc_trans; eauto.
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; try rewrite LAST_FIRST1 in *; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              rewrite VRegMap.add_add. econs; eauto.
            ** rewrite <- (app_nil_r tr3). eapply rtc_relax_base_cont in LAST_CONT; eauto.
              eapply Thread.rtc_trans; eauto.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 12. econs; eauto; ss. }
                rewrite app_nil_r. ss.
              }
              ss.
              econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              rewrite VRegMap.add_add. econs; eauto.
Qed.
