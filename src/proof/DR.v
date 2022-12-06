Require Import EquivDec.
Require Import Ensembles.
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
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
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
    hexploit loop_cases; eauto.
    { rewrite app_nil_l. ss. }
    i. des.
    + admit.
    + admit.
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
    destruct (EquivDec.equiv_dec (sem_expr (TState.regs ts0) e0) (Val.bool true)).
    + eapply IHROJ1; eauto.
    + eapply IHROJ2; eauto.
Qed.

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
        destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss. lia.
      }
      { rewrite fun_add_spec in MMT0.
        destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss. lia.
      }
      inv RTC0; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      rewrite app_nil_r in *. subst. esplits; eauto.
      { apply trace_refine_eq. }
      { i. splits; ss. apply refine_empty; ss. }
      i. splits; ss. rewrite fun_add_spec in MMT0.
      destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])); cycle 1.
      { exfalso. apply c. ss. }
      inv MMT0. ss.
    + inv RTC; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      inv ONE0. inv NORMAL_STEP; inv STEP; ss; inv STMT.
      { rewrite fun_add_spec in MMT0.
        destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss. lia.
      }
      { rewrite fun_add_spec in MMT0.
        destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss. lia.
      }
      inv RTC0; ss; cycle 1.
      { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
      rewrite app_nil_r in *. subst. esplits; eauto.
      { apply trace_refine_eq. }
      { i. splits; ss. apply refine_empty; ss. }
      i. splits; ss. rewrite fun_add_spec in MMT0.
      destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])); cycle 1.
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
        unfold Cont.Loops in RETURN0. exploit RETURN0.
        { instantiate (1 := Cont.chkptcont (TState.regs ts) r0 [] (mid ++ [lab])).
          rewrite in_app_iff. right. ss. left. ss.
        }
        i. des. ss.
      * inv CALL_DONE0; inv STEP; ss; inv STMT; inv THR2; rewrite <- rev_eq in CONT; repeat rewrite rev_app in CONT; ss. inv CONT.
        inv ONE0. inv NORMAL_STEP; inv STEP; inv STMT; ss.
        { hexploit Thread.step_time_mon; eauto. i. ss.
          rewrite fun_add_spec in *. destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])); cycle 1.
          { exfalso. apply c. ss. }
          inv MMT0. ss. lia.
        }
        inv RTC0; ss; cycle 1.
        { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
        rewrite fun_add_spec in *. destruct (EquivDec.equiv_dec (mid ++ [lab]) (mid ++ [lab])); cycle 1.
        { exfalso. apply c. ss. }
        inv MMT0. ss.
        esplits; eauto.
        { rewrite app_nil_r. eauto. }
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
      hexploit lift_cont; eauto. ss. instantiate (1 := [Cont.fncont (TState.regs ts) r []]). intros TR_X. apply relax_base in TR_X.
      esplits; [| eauto | |].
      * econs 2; eauto; cycle 1.
        { rewrite app_nil_l. ss. }
        econs; eauto. rewrite app_nil_r. ss.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx; ss.
        hexploit RETURN0.
        { instantiate (1 := Cont.fncont (TState.regs ts) r []).
          rewrite in_app_iff. right. ss. left. ss.
        }
        i. des. ss.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx0; ss.
        hexploit RETURN0.
        { instantiate (1 := Cont.fncont (TState.regs ts) r []).
          rewrite in_app_iff. right. ss. left. ss.
        }
        i. des. ss.
    + (* (ONGOING, DONE) *)
      hexploit CALL_DONE3; ss. i. clear CALL_DONE3.
      destruct thr_term. destruct thr_term'. ss. subst.
      hexploit IHF; eauto. ss. i. des.
      inversion CALL_DONE0; inv STEP; ss; inv THR2; rewrite snoc_eq_snoc in CONT; des; ss. subst.
      hexploit STOP_SND.
      { unfold STOP. repeat right. esplits; ss. }
      i. des. subst.
      inv STMT. inv CONT0.
      esplits; eauto.
      * econs 2; cycle 2.
        { rewrite app_nil_l. ss. }
        { econs; eauto. ss. rewrite app_nil_r. ss. }
        hexploit lift_cont; eauto. ss. instantiate (1 := [Cont.fncont (TState.regs ts) r0 []]). intros TR_X. apply relax_base in TR_X.
        rewrite <- (app_nil_r tr_x). eapply Thread.rtc_trans; eauto.
        econs 2.
        { econs; eauto. rewrite app_nil_l. ss. }
        { econs; eauto. }
        ss.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx; ss.
        hexploit RETURN0.
        { instantiate (1 := Cont.fncont (TState.regs ts) r0 []).
          rewrite in_app_iff. right. ss. left. ss.
        }
        i. des. ss.
    + (* (DONE, ONGOING) *)
      hexploit CALL_DONE3; ss. i. clear CALL_DONE3.
      destruct thr_term. destruct thr_term'. ss. subst.
      hexploit IHF; eauto. ss. i. des.
      inv CALL_DONE0; inv STEP; ss; inv THR2; rewrite snoc_eq_snoc in CONT; des; ss. subst.
      hexploit STOP_FST.
      { unfold STOP. repeat right. esplits; ss. }
      i. des. subst.
      inv STMT. inv CONT0.
      esplits; eauto.
      * hexploit trace_refine_app; [apply H3 | |]; cycle 1.
        { rewrite app_nil_r. eauto. }
        apply trace_refine_eq.
      * unfold STOP. unfold Cont.Loops. i. des; try by destruct c_pfx; ss.
        hexploit RETURN0.
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
      hexploit STOP_FST.
      { unfold STOP. repeat right. esplits; ss. }
      hexploit STOP_SND.
      { unfold STOP. repeat right. esplits; ss. }
      i. des. subst.
      inv STMT0. inv H0. inv STMT. inv CONT0. inv CONT1.
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
  - admit.
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
      hexploit last_loop_iter; eauto; ss.
      { rewrite app_nil_l. ss. }
      i. des. subst. rename H0 into TR3.
      symmetry in H1. rewrite <- app_nil_l in H1. apply snoc_eq_snoc in H1. des. subst. cleartriv.

      assert (s1 = stmt_chkpt r [stmt_return r] (mid ++ [lab]) :: s_body /\ c1 = [] /\ ts.(TState.time) <= ts1.(TState.time)).
      { unguard. des; splits; subst; ss.
        hexploit Thread.step_time_mon; [exact LAST_CONT |]; eauto.
      }

      des. subst. inv H2; try inv THR.
      inv ONE0. inv NORMAL_STEP0; inv STEP; ss; inv STMT.
      * (* EX1: CHKPT-CALL *)
        inv RTC0; try inv THR.
        inv ONE0. inv NORMAL_STEP0; inv STEP; ss; inv STMT; ss; cycle 1.
        { rewrite app_nil_r in CONT. destruct c_loops; ss. inv CONT. destruct c_loops; ss. }
        rewrite app_nil_r in CONT. destruct c_loops; ss; inv CONT; cycle 1.
        { destruct c_loops; ss. }
        hexploit lift_mmt; eauto. ss. instantiate (1 := mid). i. des.
        specialize COMPL_EQ with (mid ++ [lab]).
        assert (COMPL_IN: Ensembles.In (list Label) (Complement (list Label) (mmt_id_exp mid labs)) (mid ++ [lab])).
        { clear - NIN.
          unfold Ensembles.In. unfold Complement. ii.
          inv H. induction mid; inv MID; eauto.
        }
        symmetry in COMPL_EQ.
        hexploit Mmts.proj_inv; eauto.
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
            destruct thr_term, thr_term'; ss. subst.
            esplits; eauto.
            hexploit trace_refine_app; [exact H5| | ]; ss; cycle 1.
            { rewrite app_nil_r. eauto. }
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
            destruct thr_term, thr_term'; ss. subst.
            esplits; eauto.
            { hexploit trace_refine_app; [exact H4| | ]; ss; cycle 1.
              { rewrite app_nil_r. eauto. }
              apply trace_refine_eq.
            }
            unfold STOP. i. des; try by destruct c_pfx; ss.
            inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
            hexploit STOP_SND.
            { unfold STOP. repeat right. esplits; ss. }
            i. des. ss.
      * (* EX1: CHKPT-REPLAY *)
        hexploit lift_mmt; eauto. ss. instantiate (1 := mid). i. des.
        specialize COMPL_EQ with (mid ++ [lab]).
        assert (COMPL_IN: Ensembles.In (list Label) (Complement (list Label) (mmt_id_exp mid labs)) (mid ++ [lab])).
        { clear - NIN.
          unfold Ensembles.In. unfold Complement. ii.
          inv H. induction mid; inv MID; eauto.
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
            destruct thr_term, thr_term'; ss. subst.
            esplits; eauto.
            hexploit trace_refine_app; [exact H5| | ]; ss; cycle 1.
            { rewrite app_nil_r. eauto. }
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
            destruct thr_term, thr_term'; ss. subst.
            esplits; eauto.
            { hexploit trace_refine_app; [exact H4| | ]; ss; cycle 1.
              { rewrite app_nil_r. eauto. }
              apply trace_refine_eq.
            }
            unfold STOP. i. des; try by destruct c_pfx; ss.
            inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
            hexploit STOP_SND.
            { unfold STOP. repeat right. esplits; ss. }
            i. des. ss.
    + (* EX1: LOOP-ONGOING *)
      hexploit last_loop_iter; eauto; ss.
      { rewrite app_nil_l. ss. }
      i. des. rename H0 into TR3.

      assert (s1 = stmt_chkpt r [stmt_return r] (mid ++ [lab]) :: s_body /\ c1 = [] /\ ts.(TState.time) <= ts1.(TState.time)).
      { unguard. des; splits; subst; ss.
        hexploit Thread.step_time_mon; [exact LAST_CONT |]; eauto.
      }
      des. subst.

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
        hexploit lift_mmt; eauto. ss. instantiate (1 := mid). i. des.
        specialize COMPL_EQ with (mid ++ [lab]).
        assert (COMPL_IN: Ensembles.In (list Label) (Complement (list Label) (mmt_id_exp mid labs)) (mid ++ [lab])).
        { clear - NIN.
          unfold Ensembles.In. unfold Complement. ii.
          inv H. induction mid; inv MID; eauto.
        }
        symmetry in COMPL_EQ.
        hexploit Mmts.proj_inv; eauto.
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
                   (stmt_chkpt r0 [stmt_return r0] (mid ++ [lab]) :: s) []]). intro TR_X. apply relax_base in TR_X.

            eexists (tr3 ++ tr_x ++ tr2).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; [| apply trace_refine_eq].
              rewrite app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              rewrite <- (app_nil_r tr2). apply relax_base in FIRST_DONE1.
              eapply Thread.rtc_trans; eauto.
              econs 2; (try by econs; eauto); cycle 1.
              { rewrite app_nil_l. ss. }
              econs; [| rewrite app_nil_l]; ss. econs 13. econs; ss.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; ss; subst; ss.
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
            ** rewrite <- (app_nil_r tr3). apply relax_base in LAST_CONT.
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

            destruct thr_term, thr_term'; ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r0
                   (stmt_chkpt r0 [stmt_return r0] (mid ++ [lab]) :: s) []]). intro TR_X. apply relax_base in TR_X.

            eexists (tr3 ++ tr_x ++ []).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; eauto; [|apply trace_refine_eq]. rewrite app_nil_r. eauto. }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
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
            move TR3 at bottom. unguard. des; ss; subst; ss.
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
            ** rewrite <- (app_nil_r tr3). apply relax_base in LAST_CONT.
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
                   (stmt_chkpt r0 [stmt_return r0] (mid ++ [lab]) :: s) []]). intro TR_X. apply relax_base in TR_X.

            eexists (tr3 ++ tr_x ++ tr2).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; [| apply trace_refine_eq].
              rewrite app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              apply relax_base in FIRST_DONE1. ss.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; ss; subst; ss.
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
            ** rewrite <- (app_nil_r tr3). apply relax_base in LAST_CONT.
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
                   (stmt_chkpt r0 [stmt_return r0] (mid ++ [lab]) :: s) []]). intro TR_X. apply relax_base in TR_X.

            eexists (tr3 ++ tr_x). eexists s_x.
            eexists (c_x ++ [Cont.loopcont (TState.regs ts) r0 (stmt_chkpt r0 [stmt_return r0] (mid ++ [lab]) :: s) []]).
            eexists ts_x.
            splits; ss; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq. }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. subst. ss.
            }
            { unfold STOP. i. des; try by destruct c_pfx; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_SND.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. subst. ss.
            }
            eapply Thread.rtc_trans; eauto.
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; ss; subst; ss.
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
            ** rewrite <- (app_nil_r tr3). apply relax_base in LAST_CONT.
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
        hexploit lift_mmt; eauto. ss. instantiate (1 := mid). i. des.
        specialize COMPL_EQ with (mid ++ [lab]).
        assert (COMPL_IN: Ensembles.In (list Label) (Complement (list Label) (mmt_id_exp mid labs)) (mid ++ [lab])).
        { clear - NIN.
          unfold Ensembles.In. unfold Complement. ii.
          inv H. induction mid; inv MID; eauto.
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
                   (stmt_chkpt r [stmt_return r] (mid ++ [lab]) :: s0) []]). intro TR_X. apply relax_base in TR_X.

            eexists (tr3 ++ tr_x ++ tr2).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; [| apply trace_refine_eq].
              rewrite app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              rewrite <- (app_nil_r tr2). apply relax_base in FIRST_DONE1.
              eapply Thread.rtc_trans; eauto.
              econs 2; (try by econs; eauto); cycle 1.
              { rewrite app_nil_l. ss. }
              econs; [| rewrite app_nil_l]; ss. econs 13. econs; ss.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              ss. rewrite VRegMap.add_add. econs; eauto.
            ** rewrite <- (app_nil_r tr3). apply relax_base in LAST_CONT.
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

            destruct thr_term, thr_term'; ss. subst.

            hexploit lift_cont; eauto. ss.
            instantiate (1 := [Cont.loopcont (TState.regs ts) r
                   (stmt_chkpt r [stmt_return r] (mid ++ [lab]) :: s0) []]). intro TR_X. apply relax_base in TR_X.

            eexists (tr3 ++ tr_x ++ []).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; eauto; [|apply trace_refine_eq]. rewrite app_nil_r. eauto. }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
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
            move TR3 at bottom. unguard. des; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              rewrite VRegMap.add_add. econs; eauto.
            ** rewrite <- (app_nil_r tr3). apply relax_base in LAST_CONT.
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
                   (stmt_chkpt r [stmt_return r] (mid ++ [lab]) :: s0) []]). intro TR_X. apply relax_base in TR_X.

            eexists (tr3 ++ tr_x ++ tr2).
            esplits; eauto; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; [| apply trace_refine_eq].
              rewrite app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq.
            }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. ss.
            }
            eapply Thread.rtc_trans; cycle 1.
            { eapply Thread.rtc_trans; eauto.
              apply relax_base in FIRST_DONE1. ss.
            }
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              rewrite VRegMap.add_add. econs; eauto.
            ** rewrite <- (app_nil_r tr3). apply relax_base in LAST_CONT.
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
                   (stmt_chkpt r [stmt_return r] (mid ++ [lab]) :: s0) []]). intro TR_X. apply relax_base in TR_X.

            eexists (tr3 ++ tr_x). eexists s_x.
            eexists (c_x ++ [Cont.loopcont (TState.regs ts) r (stmt_chkpt r [stmt_return r] (mid ++ [lab]) :: s0) []]).
            eexists ts_x.
            splits; ss; cycle 1.
            { rewrite <- app_assoc. apply trace_refine_app; eauto. apply trace_refine_eq. }
            { unfold STOP. i. des; try by destruct c_pfx_term; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_FST.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. subst. ss.
            }
            { unfold STOP. i. des; try by destruct c_pfx; ss.
              inv RETURN. apply Cont.loops_app_distr in RETURN0. des.
              hexploit STOP_SND.
              { unfold STOP. repeat right. esplits; ss. }
              i. des. subst. ss.
            }
            eapply Thread.rtc_trans; eauto.
            econs 2; cycle 2.
            { rewrite app_nil_l. ss. }
            { econs; eauto. }
            move TR3 at bottom. unguard. des; ss; subst; ss.
            ** econs 2; cycle 2.
              { rewrite app_nil_l. ss. }
              { econs.
                { econs 9. econs; eauto. }
                rewrite app_nil_r. ss.
              }
              rewrite VRegMap.add_add. econs; eauto.
            ** rewrite <- (app_nil_r tr3). apply relax_base in LAST_CONT.
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
