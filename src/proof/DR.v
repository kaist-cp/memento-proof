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


Definition DR_concl (env: Env.t) (s: list Stmt) (tr tr': list Event.t)
           (ts: TState.t) (mmts: Mmts.t) (thr_term thr_term': Thread.t) : Prop :=
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

(* Definition H.22 *)
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

(* Definition 3.2 *)
Definition DR_main (env: Env.t) (s: list Stmt) :=
  forall tr tr' thr_term thr_term' ts mmts,
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
    Thread.rtc env [] tr' (Thread.mk s [] ts thr_term.(Thread.mmts)) thr_term' ->
  exists tr_x s_x c_x ts_x,
    Thread.rtc env [] tr_x (Thread.mk s [] ts mmts) (Thread.mk s_x c_x ts_x thr_term'.(Thread.mmts))
    /\ tr_x ~ tr ++ tr'.

Lemma DR_main_DR env s
      (DR_S: DR env s):
  DR_main env s.
Proof.
  intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  destruct (DR_S tr tr' thr_term thr_term' ts mmts EX1 EX2) as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & _ & _).
  esplits; eauto.
Qed.

Lemma DR_fold:
  forall env s,
    (forall tr tr' thr_term thr_term' ts mmts,
        Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
        Thread.rtc env [] tr' (Thread.mk s [] ts thr_term.(Thread.mmts)) thr_term' ->
      DR_concl env s tr tr' ts mmts thr_term thr_term') ->
  DR env s.
Proof. unfold DR, DR_concl. eauto. Qed.

Lemma DR_peel:
  forall env s tr tr' ts mmts thr_m thr_term thr_term',
    ~ STOP thr_term.(Thread.stmt) thr_term.(Thread.cont) ->
    DR_concl env s tr tr' ts mmts thr_m thr_term' ->
  DR_concl env s tr tr' ts mmts thr_term thr_term'.
Proof.
  unfold DR_concl. i. des. esplits; eauto. i. exfalso. eauto.
Qed.

Lemma DR_elim:
  forall env s tr tr' thr_term thr_term' ts mmts,
    DR env s ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
    Thread.rtc env [] tr' (Thread.mk s [] ts thr_term.(Thread.mmts)) thr_term' ->
  exists tr_x s_x c_x ts_x,
    Thread.rtc env [] tr_x (Thread.mk s [] ts mmts) (Thread.mk s_x c_x ts_x thr_term'.(Thread.mmts))
    /\ tr_x ~ tr ++ tr'
    /\ (STOP thr_term.(Thread.stmt) thr_term.(Thread.cont) ->
        thr_term.(Thread.stmt) = s_x /\ thr_term.(Thread.cont) = c_x /\ thr_term.(Thread.ts) = ts_x
        /\ thr_term.(Thread.mmts) = thr_term'.(Thread.mmts) /\ [] ~ tr')
    /\ (STOP thr_term'.(Thread.stmt) thr_term'.(Thread.cont) ->
        thr_term'.(Thread.stmt) = s_x /\ thr_term'.(Thread.cont) = c_x /\ thr_term'.(Thread.ts) = ts_x).
Proof.
  intros env s tr tr' thr_term thr_term' ts mmts DR_S EX1 EX2.
  exact (DR_S tr tr' thr_term thr_term' ts mmts EX1 EX2).
Qed.

Local Ltac nloop :=
  let L := fresh "L" in intro L; inv L; ss.

Local Ltac nstop :=
  let H := fresh "STOP" in
  intro H; unfold STOP in H; des; ss;
  repeat match goal with
         | [L: Cont.Loops (_ :: _) |- _] => inv L; ss
         | [L: Forall _ (_ :: _) |- _] => inv L; ss
         end.

Lemma DR_concl_fst_silent:
  forall env s tr tr' ts mmts thr_term thr_term',
    [] ~ tr ->
    ~ STOP thr_term.(Thread.stmt) thr_term.(Thread.cont) ->
    Thread.rtc env [] tr' (Thread.mk s [] ts mmts) thr_term' ->
  DR_concl env s tr tr' ts mmts thr_term thr_term'.
Proof.
  intros env s tr tr' ts mmts thr_term thr_term' SILENT NSTOP EX2.
  destruct thr_term' as [s2 c2 ts2 mmts2].
  exists tr', s2, c2, ts2. splits.
  - exact EX2.
  - rewrite <- (app_nil_l tr') at 1. apply trace_refine_app; [apply trace_refine_eq | exact SILENT].
  - intro STOP1. contradiction.
  - intros _. splits; ss.
Qed.

Lemma DR_concl_snd_silent:
  forall env s tr tr' ts mmts thr_term thr_term',
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
    [] ~ tr' ->
    thr_term'.(Thread.mmts) = thr_term.(Thread.mmts) ->
    ~ STOP thr_term'.(Thread.stmt) thr_term'.(Thread.cont) ->
  DR_concl env s tr tr' ts mmts thr_term thr_term'.
Proof.
  intros env s tr tr' ts mmts thr_term thr_term' EX1 SILENT MMTS NSTOP.
  destruct thr_term as [s1 c1 ts1 mmts1]. ss.
  exists tr, s1, c1, ts1. splits.
  - rewrite MMTS. exact EX1.
  - rewrite <- (app_nil_r tr) at 1. apply trace_refine_app; [exact SILENT | apply trace_refine_eq].
  - intros _. splits; ss.
  - intro STOP2. contradiction.
Qed.

Lemma DR_concl_same:
  forall env s tr tr' ts mmts thr_term,
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
    [] ~ tr' ->
  DR_concl env s tr tr' ts mmts thr_term thr_term.
Proof.
  intros env s tr tr' ts mmts thr_term EX1 SILENT.
  destruct thr_term as [s1 c1 ts1 mmts1].
  exists tr, s1, c1, ts1. splits.
  - exact EX1.
  - rewrite <- (app_nil_r tr) at 1. apply trace_refine_app; [exact SILENT | apply trace_refine_eq].
  - intros _. splits; ss.
  - intros _. splits; ss.
Qed.

Definition mids_of (v: option Val.t) (labs: Ensemble Label) : Ensemble (list Label) :=
  fun m => exists pfx, v = Some (Val.mid pfx) /\ Ensembles.In _ (mmt_id_exp pfx labs) m.

Lemma mids_of_disj v labs_l labs_r m
      (DISJ: Disjoint _ labs_l labs_r)
      (IN_L: Ensembles.In _ (mids_of v labs_l) m)
      (IN_R: Ensembles.In _ (mids_of v labs_r) m):
  False.
Proof.
  destruct IN_L as (pfx & V & IN_L). destruct IN_R as (pfx' & V' & IN_R). rewrite V in V'. inv V'.
  eapply disjoint_in; [eapply exp_disj_pres; exact DISJ | exact IN_L | exact IN_R].
Qed.

Lemma rw_run_mmts:
  forall env envt labs s tr ts mmts s_w c_w ts_w mmts_w,
    TypeSystem.env_ok env envt ->
    EnvType.rw_judge envt labs s ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  Mmts.agree_on (Complement _ (mids_of (ts.(TState.regs) mid) labs)) mmts mmts_w
  /\ forall mmts_a,
      Thread.rtc env [] tr
        (Thread.mk s [] ts (Mmts.merge (mids_of (ts.(TState.regs) mid) labs) mmts mmts_a))
        (Thread.mk s_w c_w ts_w (Mmts.merge (mids_of (ts.(TState.regs) mid) labs) mmts_w mmts_a)).
Proof.
  intros. eapply lift_mmt_gen; eauto. intros pfx MID m IN. exists pfx. split; ss.
Qed.

Lemma seq_left_lift:
  forall env tr s_l s_r ts mmts ts1 mmts1,
    Thread.rtc env [] tr (Thread.mk s_l [] ts mmts) (Thread.mk [] [] ts1 mmts1) ->
  Thread.rtc env [] tr (Thread.mk (s_l ++ s_r) [] ts mmts) (Thread.mk s_r [] ts1 mmts1).
Proof.
  intros env tr s_l s_r ts mmts ts1 mmts1 RTC.
  hexploit (@seq_lifting env tr s_l [] ts mmts [] [] ts1 mmts1 s_r RTC).
  intros (s_m1 & s_m2 & c_m1 & c_m2 & LIFT & SC1 & SC2).
  rewrite seq_sc_nil in SC1, SC2. inv SC1. inv SC2. exact LIFT.
Qed.

Lemma seq_ne_guard (s: list Stmt) (c: list Cont.t)
      (NE: (s, c) <> ([], [])):
  __guard__ (s <> [] \/ c <> []).
Proof.
  unguard. destruct s as [|x s]; [|left; ss]. destruct c as [|y c]; [exfalso; apply NE; ss | right; ss].
Qed.

Lemma DR_stop:
  forall env s, STOP s [] -> DR env s.
Proof.
  intros env s STOP_S. apply DR_fold. intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  hexploit stop_means_no_step; [|exact EX1|]; [exact STOP_S|]. intros [THR1 TR1]. subst.
  hexploit stop_means_no_step; [|exact EX2|]; [exact STOP_S|]. intros [THR2 TR2]. subst.
  apply DR_concl_same; [econs | apply trace_refine_eq].
Qed.

Lemma DR_assign:
  forall env r e, DR env [stmt_assign r e].
Proof.
  intros env r e. apply DR_fold. intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  destruct (rtc_nil_inv EX1) as [[TR1 THR1] | (tr1 & tr1' & thr1 & TR1 & STEP1 & RTC1)]; subst.
  { apply DR_concl_fst_silent; [apply trace_refine_eq | nstop | exact EX2]. }
  destruct (rtc_nil_inv EX2) as [[TR2 THR2] | (tr2 & tr2' & thr2 & TR2 & STEP2 & RTC2)]; subst.
  { apply DR_concl_snd_silent; [exact EX1 | apply trace_refine_eq | reflexivity | nstop]. }
  destruct (step_assign_inv STEP1) as [TR1a (v1 & EVAL1 & THR1)]. subst.
  hexploit stop_means_no_step; [|exact RTC1|]; [left; ss|]. intros [THR_TERM TR1b]. subst.
  destruct (step_assign_inv STEP2) as [TR2a (v2 & EVAL2 & THR2)]. subst.
  rewrite EVAL1 in EVAL2. injection EVAL2 as <-.
  hexploit stop_means_no_step; [|exact RTC2|]; [left; ss|]. intros [THR_TERM' TR2b]. subst.
  apply DR_concl_same; [exact EX1 | apply trace_refine_eq].
Qed.

Lemma DR_pcas:
  forall env r e_loc e_old e_new e_mid, DR env [stmt_pcas r e_loc e_old e_new e_mid].
Proof.
  intros env r e_loc e_old e_new e_mid. apply DR_fold. intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  destruct (rtc_nil_inv EX1) as [[TR1 THR1] | (tr1 & tr1' & thr1 & TR1 & STEP1 & RTC1)]; subst.
  { apply DR_concl_fst_silent; [apply trace_refine_eq | nstop | exact EX2]. }
  destruct (rtc_nil_inv EX2) as [[TR2 THR2] | (tr2 & tr2' & thr2 & TR2 & STEP2 & RTC2)]; subst.
  { apply DR_concl_snd_silent; [exact EX1 | apply trace_refine_eq | reflexivity | nstop]. }
  assert (DONE1: exists m,
             sem_expr ts.(TState.regs) e_mid = Some (Val.mid m)
             /\ ts.(TState.time) < (thr1.(Thread.mmts) m).(Mmt.time)
             /\ thr1 = Thread.mk [] []
                         (TState.mk (VRegMap.add r (thr1.(Thread.mmts) m).(Mmt.val) ts.(TState.regs))
                                    (thr1.(Thread.mmts) m).(Mmt.time))
                         thr1.(Thread.mmts)).
  { destruct (step_pcas_inv STEP1) as [(m & v_r & t & EVAL & LE & LT & THR) | (m & EVAL & LT & TR & THR)];
      subst; ss.
    - exists m. rewrite fun_add_spec_eq. splits; ss.
    - exists m. splits; ss.
  }
  destruct DONE1 as (m & EVAL & LT & THR1).
  hexploit stop_means_no_step; [|exact RTC1|]; [rewrite THR1; left; ss|]. intros [THR_TERM TR1b]. subst.
  hexploit pcas_replay_forced; [exact STEP2 | exact EVAL | exact LT |]. intros [TR2a THR2]. subst.
  hexploit stop_means_no_step; [|exact RTC2|]; [left; ss|]. intros [THR_TERM' TR2b]. subst.
  rewrite <- THR1. apply DR_concl_same; [exact EX1 | apply trace_refine_eq].
Qed.

Lemma DR_chkpt:
  forall env envt r s_c e_mid
    (OK: TypeSystem.env_ok env envt)
    (RO: EnvType.ro_judge envt s_c),
  DR env [stmt_chkpt r s_c e_mid].
Proof.
  intros env envt r s_c e_mid OK RO. apply DR_fold. intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  destruct (rtc_nil_inv EX1) as [[TR1 THR1] | (tr1 & tr1' & thr1 & TR1 & STEP1 & RTC1)]; subst.
  { apply DR_concl_fst_silent; [apply trace_refine_eq | nstop | exact EX2]. }
  destruct (rtc_nil_inv EX2) as [[TR2 THR2] | (tr2 & tr2' & thr2 & TR2 & STEP2 & RTC2)]; subst.
  { apply DR_concl_snd_silent; [exact EX1 | apply trace_refine_eq | reflexivity | nstop]. }
  destruct (step_chkpt_inv STEP1) as [TR1a (m & EVAL & [(LE & THR1) | (LT & THR1)])]; subst.
  - (* chkpt-call *)
    hexploit (@chkpt_fn_cases env [] tr1' _ _ [] (Cont.chkptcont (TState.regs ts) r [] m) [] RTC1);
      [reflexivity | nloop |].
    intros [(c_pfx & CONT & BODY1) | (tr_b & tr_r & s_r & c_r & ts_r & mmts_r & e_r & TR & BODY1 & RET & LOOPS)].
    + (* the checkpoint body is running *)
      destruct thr_term as [s1 c1 ts1 mmts1]. ss.
      hexploit ro_run; [exact OK | exact RO | exact BODY1 |]. intros (SILENT & MMTS & _). subst mmts1.
      apply DR_concl_fst_silent; [exact SILENT | | exact EX2].
      ss. rewrite CONT. intro STOP1. eapply STOP_app_nonloop; [exact STOP1 | nloop].
    + (* the checkpoint body returned *)
      ss. hexploit ro_run; [exact OK | exact RO | exact BODY1 |]. intros (SILENT & MMTS & TIME). subst mmts_r.
      destruct (tc_nil_inv RET) as (tr_c & tr_d & thr_c & TR_R & STEP_R & RTC_R).
      hexploit step_return_inv; [exact STEP_R | exact LOOPS | nloop |].
      intros [TR_C (v & EVAL_R & t & LT & THR_C)]. subst.
      hexploit stop_means_no_step; [|exact RTC_R|]; [left; ss|]. intros [THR_TERM TR_D]. subst.
      hexploit chkpt_replay_forced; [exact STEP2 | exact EVAL | ss; rewrite fun_add_spec_eq; ss; lia |].
      intros [TR2a THR2]. subst.
      hexploit stop_means_no_step; [|exact RTC2|]; [left; ss|]. intros [THR_TERM' TR2b]. subst.
      ss. rewrite fun_add_spec_eq. ss.
      apply DR_concl_same; [exact EX1 | apply trace_refine_eq].
  - (* chkpt-replay *)
    hexploit stop_means_no_step; [|exact RTC1|]; [left; ss|]. intros [THR_TERM TR1b]. subst.
    hexploit chkpt_replay_forced; [exact STEP2 | exact EVAL | exact LT |]. intros [TR2a THR2]. subst.
    hexploit stop_means_no_step; [|exact RTC2|]; [left; ss|]. intros [THR_TERM' TR2b]. subst.
    apply DR_concl_same; [exact EX1 | apply trace_refine_eq].
Qed.

Lemma fn_return_stop:
  forall env tr e s_rem c_r rmap r ts mmts thr_term,
    Thread.tc env [] tr
      (Thread.mk (stmt_return e :: s_rem) (c_r ++ [Cont.fncont rmap r []]) ts mmts) thr_term ->
    Cont.Loops c_r ->
  tr = []
  /\ exists v,
      sem_expr ts.(TState.regs) e = Some v
      /\ thr_term = Thread.mk [] [] (TState.mk (VRegMap.add r v rmap) ts.(TState.time)) mmts.
Proof.
  intros env tr e s_rem c_r rmap r ts mmts thr_term TC LOOPS.
  destruct (tc_nil_inv TC) as (tr0 & tr1 & thr0 & TR & STEP & RTC).
  hexploit step_return_inv; [exact STEP | exact LOOPS | nloop |]. intros [TR0 (v & EVAL & THR0)]. subst.
  hexploit stop_means_no_step; [|exact RTC|]; [left; ss|]. intros [THR TR1]. subst. eauto.
Qed.

Lemma DR_call:
  forall env r f es prms s_f
    (FIND_F: IdMap.find f env = Some (prms, s_f))
    (IH_F: DR env s_f),
  DR env [stmt_call r f es].
Proof.
  intros env r f es prms s_f FIND_F IH_F. apply DR_fold.
  intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  destruct (rtc_nil_inv EX1) as [[TR1 THR1] | (tr1 & tr1' & thr1 & TR1 & STEP1 & RTC1)]; subst.
  { apply DR_concl_fst_silent; [apply trace_refine_eq | nstop | exact EX2]. }
  destruct (rtc_nil_inv EX2) as [[TR2 THR2] | (tr2 & tr2' & thr2 & TR2 & STEP2 & RTC2)]; subst.
  { apply DR_concl_snd_silent; [exact EX1 | apply trace_refine_eq | reflexivity | nstop]. }
  destruct (step_call_inv STEP1) as [TR1a (vs1 & prms1 & s_f1 & EVAL1 & FIND1 & LEN1 & THR1)].
  destruct (step_call_inv STEP2) as [TR2a (vs2 & prms2 & s_f2 & EVAL2 & FIND2 & LEN2 & THR2)].
  rewrite FIND_F in FIND1, FIND2. injection FIND1 as <- <-. injection FIND2 as <- <-.
  rewrite EVAL1 in EVAL2. injection EVAL2 as <-. subst. ss.
  set (cts := TState.mk (bind_params prms vs1) (TState.time ts)) in *.
  hexploit (@chkpt_fn_cases env [] tr1' _ _ [] (Cont.fncont (TState.regs ts) r []) [] RTC1);
    [reflexivity | nloop |].
  intros [(c_pfx1 & CONT1 & L1) | (tr1a & tr1b & s_r1 & c_r1 & ts_r1 & mmts_r1 & e_r1 & TR1b & L1 & RET1 & LOOPS1)];
  (hexploit (@chkpt_fn_cases env [] tr2' _ _ [] (Cont.fncont (TState.regs ts) r []) [] RTC2);
    [reflexivity | nloop |]);
  (intros [(c_pfx2 & CONT2 & L2) | (tr2a & tr2b & s_r2 & c_r2 & ts_r2 & mmts_r2 & e_r2 & TR2b & L2 & RET2 & LOOPS2)]);
  ss.
  - (* call-ongoing, call-ongoing *)
    destruct (DR_elim IH_F L1 L2)
    as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND).
    exists tr_x, s_x, (c_x ++ [Cont.fncont (TState.regs ts) r []]), ts_x. splits.
    + eapply rtc_nil_step; [exact STEP1 | eapply rtc_lift_nil in TRACE; exact TRACE | reflexivity].
    + exact REFINE.
    + rewrite CONT1. intro STOP1. exfalso. eapply STOP_app_nonloop; [exact STOP1 | nloop].
    + rewrite CONT2. intro STOP2. exfalso. eapply STOP_app_nonloop; [exact STOP2 | nloop].
  - (* call-ongoing, call-done *)
    destruct (DR_elim IH_F L1 L2)
    as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND). ss.
    hexploit STOP_SND; [right; right; right; esplits; eauto|]. intros (S & C & TS). subst s_x c_x ts_x.
    destruct thr_term' as [s' c' ts' mmts'].
    exists (tr_x ++ tr2b), s', c', ts'. splits.
    + eapply rtc_nil_step; [exact STEP1 | | reflexivity].
      eapply rtc_app; [eapply rtc_lift_nil in TRACE; exact TRACE | apply tc_rtc; exact RET2 | reflexivity].
    + subst. rewrite app_assoc. apply trace_refine_app; [apply trace_refine_eq | exact REFINE].
    + rewrite CONT1. intro STOP1. exfalso. eapply STOP_app_nonloop; [exact STOP1 | nloop].
    + intros _. splits; ss.
  - (* call-done, call-ongoing *)
    hexploit fn_return_stop; [exact RET1 | exact LOOPS1 |]. intros [TR (v1 & EVAL_V1 & THR)]. subst.
    destruct (DR_elim IH_F L1 L2)
    as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND). ss.
    hexploit STOP_FST; [right; right; right; esplits; eauto|]. intros (S & C & TS & MMTS & SILENT).
    apply DR_concl_snd_silent; [exact EX1 | exact SILENT | symmetry; exact MMTS |].
    rewrite CONT2. intro STOP2. eapply STOP_app_nonloop; [exact STOP2 | nloop].
  - (* call-done, call-done *)
    hexploit fn_return_stop; [exact RET1 | exact LOOPS1 |]. intros [TR (v1 & EVAL_V1 & THR)]. subst.
    hexploit fn_return_stop; [exact RET2 | exact LOOPS2 |]. intros [TR' (v2 & EVAL_V2 & THR')]. subst.
    destruct (DR_elim IH_F L1 L2)
    as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND). ss.
    hexploit STOP_FST; [right; right; right; esplits; eauto|]. intros (S & C & TS & MMTS & SILENT).
    hexploit STOP_SND; [right; right; right; esplits; eauto|]. intros (S' & C' & TS').
    subst s_x ts_r1 ts_r2 mmts_r2. injection S' as E_R S_R. subst e_r2.
    rewrite EVAL_V1 in EVAL_V2. injection EVAL_V2 as <-.
    apply DR_concl_same; [exact EX1 | rewrite app_nil_r; exact SILENT].
Qed.

Lemma DR_ite:
  forall env e s_t s_f
    (IH_T: DR env s_t)
    (IH_F: DR env s_f),
  DR env [stmt_if e s_t s_f].
Proof.
  intros env e s_t s_f IH_T IH_F. apply DR_fold. intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  destruct (rtc_nil_inv EX1) as [[TR1 THR1] | (tr1 & tr1' & thr1 & TR1 & STEP1 & RTC1)]; subst.
  { apply DR_concl_fst_silent; [apply trace_refine_eq | nstop | exact EX2]. }
  destruct (rtc_nil_inv EX2) as [[TR2 THR2] | (tr2 & tr2' & thr2 & TR2 & STEP2 & RTC2)]; subst.
  { apply DR_concl_snd_silent; [exact EX1 | apply trace_refine_eq | reflexivity | nstop]. }
  destruct (step_if_inv STEP1) as [TR1a (b1 & EVAL1 & THR1)].
  destruct (step_if_inv STEP2) as [TR2a (b2 & EVAL2 & THR2)].
  rewrite EVAL1 in EVAL2. injection EVAL2 as <-. subst.
  rewrite app_nil_r in STEP1, RTC1, RTC2.
  assert (IH: DR env (if b1 then s_t else s_f)) by (destruct b1; ss).
  destruct (DR_elim IH RTC1 RTC2)
  as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND).
  exists tr_x, s_x, c_x, ts_x. splits.
  - eapply rtc_nil_step; [exact STEP1 | exact TRACE | reflexivity].
  - exact REFINE.
  - exact STOP_FST.
  - exact STOP_SND.
Qed.

Lemma DR_seq:
  forall env envt labs_l labs_r s_l s_r
    (OK: TypeSystem.env_ok env envt)
    (DISJ: Disjoint _ labs_l labs_r)
    (LEFT: EnvType.rw_judge envt labs_l s_l)
    (RIGHT: EnvType.rw_judge envt labs_r s_r)
    (IH_L: DR env s_l)
    (IH_R: DR env s_r),
  DR env (s_l ++ s_r).
Proof.
  intros env envt labs_l labs_r s_l s_r OK DISJ LEFT RIGHT IH_L IH_R. apply DR_fold.
  intros tr tr' [s1 c1 ts1 mmts1] [s2 c2 ts2 mmts2] ts mmts EX1 EX2. ss.
  hexploit seq_cases; [exact EX1|].
  intros [(s_m1 & c_m1 & L1 & SC1 & NE1) | (tr_l1 & tr_r1 & ts_l1 & mmts_l1 & TR1 & L1 & R1)].
  - hexploit seq_cases; [exact EX2|].
    intros [(s_m2 & c_m2 & L2 & SC2 & NE2) | (tr_l2 & tr_r2 & ts_l2 & mmts_l2 & TR2 & L2 & R2)].
    + (* left-ongoing, left-ongoing *)
      destruct (DR_elim IH_L L1 L2)
      as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND). ss.
      hexploit (@seq_lifting env tr_x s_l [] ts mmts s_x c_x ts_x mmts2 s_r TRACE).
      intros (s_a & s_b & c_a & c_b & LIFT & SCA & SCB).
      rewrite seq_sc_nil in SCA. inv SCA.
      exists tr_x, s_b, c_b, ts_x. splits.
      * exact LIFT.
      * exact REFINE.
      * intro STOP1.
        hexploit seq_sc_stop; [apply seq_ne_guard; exact NE1 | symmetry; exact SC1 |]. intros [_ STOP_M1].
        hexploit STOP_FST; [apply STOP_M1; exact STOP1 |]. intros (S & C & TS & MMTS & SILENT). subst.
        rewrite <- SC1 in SCB. inv SCB. splits; ss.
      * intro STOP2.
        hexploit seq_sc_stop; [apply seq_ne_guard; exact NE2 | symmetry; exact SC2 |]. intros [_ STOP_M2].
        hexploit STOP_SND; [apply STOP_M2; exact STOP2 |]. intros (S & C & TS). subst.
        rewrite <- SC2 in SCB. inv SCB. splits; ss.
    + (* left-ongoing, left-done *)
      destruct (DR_elim IH_L L1 L2)
      as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND). ss.
      hexploit STOP_SND; [left; ss|]. intros (S & C & TS). subst s_x c_x ts_x.
      exists (tr_x ++ tr_r2), s2, c2, ts2. splits.
      * eapply rtc_app; [eapply seq_left_lift; exact TRACE | exact R2 | reflexivity].
      * subst. rewrite app_assoc. apply trace_refine_app; [apply trace_refine_eq | exact REFINE].
      * intro STOP1. exfalso.
        hexploit seq_sc_stop; [apply seq_ne_guard; exact NE1 | symmetry; exact SC1 |]. intros [_ STOP_M1].
        hexploit STOP_FST; [apply STOP_M1; exact STOP1 |]. intros (S & C & _). subst. ss.
      * intros _. splits; ss.
  - (* left-done *)
    subst tr.
    hexploit rw_mid_top; [exact OK | exact LEFT | exact L1 |]. intro MID1.
    set (mids_l := mids_of (TState.regs ts mid) labs_l).
    hexploit rw_run_mmts; [exact OK | exact RIGHT | exact R1 |]. intros (AGREE_R & _).
    rewrite MID1 in AGREE_R.
    assert (AGREE: forall m, Ensembles.In _ mids_l m -> mmts1 m = mmts_l1 m).
    { intros m IN. symmetry. apply AGREE_R. intro IN_R. eapply mids_of_disj; [exact DISJ | exact IN | exact IN_R]. }
    assert (BACK: forall mmts2 m,
               Mmts.agree_on (Complement _ mids_l) mmts1 mmts2 ->
               mmts_l1 m = Mmts.merge mids_l mmts2 mmts_l1 m ->
               mmts2 m = mmts1 m).
    { intros mmts2' m OUT EQ. destruct (classic (Ensembles.In _ mids_l m)) as [IN | NIN].
      - rewrite merge_in in EQ; ss. rewrite <- EQ. symmetry. apply AGREE. ss.
      - symmetry. apply OUT. ss.
    }
    assert (MERGE: Mmts.merge mids_l mmts1 mmts_l1 = mmts_l1).
    { funext. intro m. destruct (classic (Ensembles.In _ mids_l m)) as [IN | NIN].
      - rewrite merge_in; ss. apply AGREE. ss.
      - rewrite merge_out; ss.
    }
    hexploit seq_cases; [exact EX2|].
    intros [(s_m2 & c_m2 & L2 & SC2 & NE2) | (tr_l2 & tr_r2 & ts_l2 & mmts_l2 & TR2 & L2 & R2)].
    + (* left-done, left-ongoing *)
      hexploit rw_run_mmts; [exact OK | exact LEFT | exact L2 |]. intros (OUT2 & FRAME2).
      fold mids_l in OUT2, FRAME2. specialize (FRAME2 mmts_l1). rewrite MERGE in FRAME2.
      destruct (DR_elim IH_L L1 FRAME2)
      as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND). ss.
      hexploit STOP_FST; [left; ss|]. intros (S & C & TS & MMTS & SILENT). subst s_x c_x ts_x.
      apply DR_concl_snd_silent; [exact EX1 | exact SILENT | |].
      * ss. funext. intro m. eapply BACK; [exact OUT2 | exact (equal_f MMTS m)].
      * ss. intro STOP2.
        hexploit seq_sc_stop; [apply seq_ne_guard; exact NE2 | symmetry; exact SC2 |]. intros [_ STOP_M2].
        hexploit STOP_SND; [apply STOP_M2; exact STOP2 |]. intros (S & C & _). subst. ss.
    + (* left-done, left-done *)
      hexploit rw_run_mmts; [exact OK | exact LEFT | exact L2 |]. intros (OUT2 & FRAME2).
      fold mids_l in OUT2, FRAME2. specialize (FRAME2 mmts_l1). rewrite MERGE in FRAME2.
      destruct (DR_elim IH_L L1 FRAME2)
      as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND). ss.
      hexploit STOP_FST; [left; ss|]. intros (S & C & TS & MMTS & SILENT). subst s_x c_x ts_x.
      hexploit STOP_SND; [left; ss|]. intros (_ & _ & TS2). subst ts_l2.
      assert (MMTS2: mmts_l2 = mmts1).
      { funext. intro m. eapply BACK; [exact OUT2 | exact (equal_f MMTS m)]. }
      subst mmts_l2 tr'.
      destruct (DR_elim IH_R R1 R2)
      as (tr_y & s_y & c_y & ts_y & TRACE_R & REFINE_R & STOP_FST_R & STOP_SND_R). ss.
      exists (tr_l1 ++ tr_y), s_y, c_y, ts_y. splits.
      * eapply rtc_app; [eapply seq_left_lift; exact L1 | exact TRACE_R | reflexivity].
      * rewrite <- app_assoc. apply trace_refine_app; [|apply trace_refine_eq].
        apply trace_refine_nil_ins; [exact REFINE_R | exact SILENT].
      * intro STOP1. hexploit STOP_FST_R; [exact STOP1|]. intros (S & C & TS & MMTS' & SILENT_R).
        splits; ss. rewrite <- (app_nil_l []). apply trace_refine_app; ss.
      * exact STOP_SND_R.
Qed.

Local Notation LBODY r lab s_body :=
  (stmt_chkpt r [stmt_return (expr_reg r)] (expr_mid lab) :: s_body) (only parsing).
Local Notation LCONT ts r lab s_body :=
  (Cont.loopcont (TState.regs ts) (Some r)
                 (stmt_chkpt r [stmt_return (expr_reg r)] (expr_mid lab) :: s_body) []) (only parsing).
Local Notation LTS r v ts :=
  (TState.mk (VRegMap.add r v (TState.regs ts)) (TState.time ts)) (only parsing).

Definition loop_prefix (env: Env.t) (r: VReg) (lab: Label) (s_body: list Stmt)
           (ts: TState.t) (v0: Val.t) (mmts: Mmts.t)
           (tr_h: list Event.t) (ts_h: TState.t) (mmts_h: Mmts.t) : Prop :=
  (ts_h = LTS r v0 ts /\ mmts_h = mmts /\ tr_h = [])
  \/ (exists e0 s_r ts_r v,
        Thread.rtc env [LCONT ts r lab s_body] tr_h
          (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts)
          (Thread.mk (stmt_continue e0 :: s_r) [LCONT ts r lab s_body] ts_r mmts_h)
        /\ sem_expr ts_r.(TState.regs) e0 = Some v
        /\ ts_h = TState.mk (VRegMap.add r v (TState.regs ts)) (TState.time ts_r)).

Lemma loop_prefix_rtc:
  forall env r e lab s_body ts v0 mmts tr_h ts_h mmts_h,
    sem_expr ts.(TState.regs) e = Some v0 ->
    loop_prefix env r lab s_body ts v0 mmts tr_h ts_h mmts_h ->
  Thread.rtc env [] tr_h
    (Thread.mk [stmt_loop (Some r) e (LBODY r lab s_body)] [] ts mmts)
    (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] ts_h mmts_h)
  /\ TState.time ts <= TState.time ts_h
  /\ exists v, TState.regs ts_h = VRegMap.add r v (TState.regs ts).
Proof.
  intros env r e lab s_body ts v0 mmts tr_h ts_h mmts_h EVAL0 PFX.
  assert (LOOP: Thread.step env []
                  (Thread.mk [stmt_loop (Some r) e (LBODY r lab s_body)] [] ts mmts)
                  (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts)).
  { exact (@Thread.step_loop env (Some r) e (LBODY r lab s_body) [] [] ts mmts v0 EVAL0). }
  destruct PFX as [(TS_H & MMTS_H & TR_H) | (e0 & s_r & ts_r & v & ITERS & EVAL & TS_H)]; subst.
  - splits.
    + eapply rtc_nil_step; [exact LOOP | econs | reflexivity].
    + ss.
    + exists v0. ss.
  - hexploit Thread.step_time_mon; [exact ITERS|]. ss. intro TIME.
    splits.
    + eapply rtc_nil_step; [exact LOOP | | reflexivity].
      eapply rtc_app; [eapply rtc_relax_base_cont; [exact ITERS | symmetry; apply app_nil_r] | |].
      * eapply rtc_nil_step; [| econs | reflexivity].
        exact (@Thread.step_continue env e0 s_r [LCONT ts r lab s_body] ts_r mmts_h v (TState.regs ts) (Some r)
                                     (LBODY r lab s_body) [] [] EVAL eq_refl).
      * rewrite app_nil_r. reflexivity.
    + ss.
    + exists v. ss.
Qed.

Lemma loop_last_iter:
  forall env r lab s_body ts v0 mmts tr thr_term,
    Thread.rtc env [LCONT ts r lab s_body] tr
      (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts) thr_term ->
  exists tr_h tr_l ts_h mmts_h c_pfx_term,
    tr = tr_h ++ tr_l
    /\ loop_prefix env r lab s_body ts v0 mmts tr_h ts_h mmts_h
    /\ thr_term.(Thread.cont) = c_pfx_term ++ [LCONT ts r lab s_body]
    /\ Thread.rtc env [] tr_l
         (Thread.mk (LBODY r lab s_body) [] ts_h mmts_h)
         (Thread.mk thr_term.(Thread.stmt) c_pfx_term thr_term.(Thread.ts) thr_term.(Thread.mmts)).
Proof.
  intros env r lab s_body ts v0 mmts tr thr_term RTC.
  hexploit (@last_loop_iter env tr _ _ [] (TState.regs ts) (Some r) (LBODY r lab s_body) RTC); [reflexivity |].
  intros (tr_h & tr_l & s1 & c1 & ts1 & mmts1 & c_pfx_term & TR & LAST & CONT & ITER).
  destruct LAST as [(S1 & C1 & TS1 & MMTS1 & TR_H) | (e0 & s_r & ts_r & v & ITERS & EVAL & S1 & C1 & TS1)];
    subst; ss.
  - exists [], tr_l, (LTS r v0 ts), mmts, c_pfx_term. splits; ss. left. splits; ss.
  - exists tr_h, tr_l, (TState.mk (VRegMap.add r v (TState.regs ts)) (TState.time ts_r)), mmts1, c_pfx_term.
    splits; ss. right. esplits; eauto.
Qed.

Lemma loop_body_cases:
  forall env r lab s_body ts1 mmts1 tr thr_end,
    Thread.rtc env [] tr (Thread.mk (LBODY r lab s_body) [] ts1 mmts1) thr_end ->
  (tr = [] /\ thr_end = Thread.mk (LBODY r lab s_body) [] ts1 mmts1)
  \/ (exists m, tr = [] /\ thr_end = Thread.mk [stmt_return (expr_reg r)]
                                [Cont.chkptcont (TState.regs ts1) r s_body m] ts1 mmts1)
  \/ (exists m mmt mmts_c,
        sem_expr ts1.(TState.regs) (expr_mid lab) = Some (Val.mid m)
        /\ mmts_c m = mmt
        /\ TState.time ts1 < Mmt.time mmt
        /\ Thread.rtc env [] []
             (Thread.mk (LBODY r lab s_body) [] ts1 mmts1)
             (Thread.mk s_body [] (TState.mk (VRegMap.add r (Mmt.val mmt) (TState.regs ts1)) (Mmt.time mmt)) mmts_c)
        /\ Thread.rtc env [] tr
             (Thread.mk s_body [] (TState.mk (VRegMap.add r (Mmt.val mmt) (TState.regs ts1)) (Mmt.time mmt)) mmts_c)
             thr_end).
Proof.
  intros env r lab s_body ts1 mmts1 tr thr_end RTC.
  destruct (rtc_nil_inv RTC) as [[TR THR] | (tr0 & tr1 & thr0 & TR & STEP & RTC0)]; subst.
  { left. split; ss. }
  right. destruct (step_chkpt_inv STEP) as [TR0 (m & EVAL & [(LE & THR0) | (LT & THR0)])]; subst.
  - destruct (rtc_nil_inv RTC0) as [[TR1 THR1] | (tr2 & tr3 & thr2 & TR1 & STEP2 & RTC2)]; subst.
    { left. exists m. split; ss. }
    right.
    hexploit (@step_return_inv env tr2 _ _ [] _ [] _ _ _ STEP2); [econs | nloop |].
    intros [TR2 (v & EVAL_V & t & LT & THR2)]. subst.
    exists m, (Mmt.mk v t), (fun_add m (Mmt.mk v t) mmts1). splits.
    + exact EVAL.
    + apply fun_add_spec_eq.
    + ss.
    + eapply rtc_nil_step; [exact STEP | eapply rtc_nil_step; [exact STEP2 | econs | reflexivity] | reflexivity].
    + exact RTC2.
  - right. exists m, (mmts1 m), mmts1. splits.
    + exact EVAL.
    + reflexivity.
    + exact LT.
    + eapply rtc_nil_step; [exact STEP | econs | reflexivity].
    + exact RTC0.
Qed.

Lemma loop_body_mmt:
  forall env envt labs' s_body lab pfx ts mmts tr s_w c_w ts_w mmts_w,
    TypeSystem.env_ok env envt ->
    EnvType.rw_judge envt labs' s_body ->
    ~ Ensembles.In Label labs' lab ->
    ts.(TState.regs) mid = Some (Val.mid pfx) ->
    Thread.rtc env [] tr (Thread.mk s_body [] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  mmts_w (pfx ++ [lab]) = mmts (pfx ++ [lab]).
Proof.
  intros env envt labs' s_body lab pfx ts mmts tr s_w c_w ts_w mmts_w OK BODY NIN MID RTC.
  hexploit lift_mmt_ok; [exact OK | exact BODY | exact MID | exact RTC |]. intros (AGREE & _).
  symmetry. apply AGREE. intro IN. inv IN. apply app_inv_head in MID0. inv MID0. contradiction.
Qed.

Lemma loop_head_replay:
  forall env (r: VReg) lab s_body ts v0 ts_h mmts' m tr0 thr0,
    TState.time ts <= TState.time ts_h ->
    sem_expr (VRegMap.add r v0 (TState.regs ts)) (expr_mid lab) = Some (Val.mid m) ->
    (exists v, TState.regs ts_h = VRegMap.add r v (TState.regs ts)) ->
    TState.time ts_h < Mmt.time (mmts' m) ->
    Thread.step env tr0 (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts') thr0 ->
  tr0 = []
  /\ thr0 = Thread.mk s_body [LCONT ts r lab s_body]
              (TState.mk (VRegMap.add r (Mmt.val (mmts' m)) (TState.regs ts_h)) (Mmt.time (mmts' m)))
              mmts'.
Proof.
  intros env r lab s_body ts v0 ts_h mmts' m tr0 thr0 TIME EVAL (v & REGS) LT STEP.
  hexploit chkpt_replay_forced; [exact STEP | exact EVAL | ss; lia |]. intros [TR0 THR0]. subst.
  split; [reflexivity|]. ss. rewrite REGS, ! VRegMap.add_add. reflexivity.
Qed.

Lemma loop_iter_split:
  forall env rmap r s_b tr s ts mmts thr_term,
    Thread.rtc env [] tr (Thread.mk s [Cont.loopcont rmap r s_b []] ts mmts) thr_term ->
  exists tr_a tr_b s2 c2 ts2 mmts2,
    tr = tr_a ++ tr_b
    /\ Thread.rtc env [] tr_a (Thread.mk s [] ts mmts) (Thread.mk s2 c2 ts2 mmts2)
    /\ Thread.rtc env [] tr_b (Thread.mk s2 (c2 ++ [Cont.loopcont rmap r s_b []]) ts2 mmts2) thr_term
    /\ (STOP s2 c2
        \/ (tr_b = [] /\ thr_term = Thread.mk s2 (c2 ++ [Cont.loopcont rmap r s_b []]) ts2 mmts2)).
Proof.
  intros env rmap r s_b tr s ts mmts thr_term RTC.
  hexploit (@loop_cases env [] tr _ _ [] rmap r s_b [] RTC); [reflexivity |].
  intros [ONG | (tr0 & tr1 & s_r & ts_r & mmts_r & TR & BRK & OUT)].
  - hexploit (@first_loop_iter env tr _ _ [] rmap r s_b ONG); [reflexivity |].
    intros [(c_pfx & CONT & FST) | (tr1 & tr2 & e & s1 & ts1 & mmts1 & TR & FST & REST)].
    + destruct thr_term as [s' c' ts' mmts']. ss. subst.
      exists tr, [], s', c_pfx, ts', mmts'. splits.
      * rewrite app_nil_r. reflexivity.
      * exact FST.
      * econs.
      * right. split; reflexivity.
    + exists tr1, tr2, (stmt_continue e :: s1), [], ts1, mmts1. splits.
      * exact TR.
      * exact FST.
      * eapply rtc_relax_base_cont; [exact REST | symmetry; apply app_nil_r].
      * left. right. right. left. esplits; eauto.
  - hexploit stop_means_no_step; [|exact OUT|]; [left; ss|]. intros [THR TR1]. subst.
    hexploit (@first_loop_iter env tr0 _ _ [] rmap r s_b BRK); [reflexivity |].
    intros [(c_pfx & CONT & FST) | (tr2 & tr3 & e & s1 & ts1 & mmts1 & TR & FST & REST)]; ss.
    + assert (c_pfx = []).
      { destruct c_pfx as [|c0 c_pfx]; ss. inv CONT. destruct c_pfx; ss. }
      subst c_pfx.
      exists tr0, [], (stmt_break :: s_r), [], ts_r, mmts_r. splits.
      * reflexivity.
      * exact FST.
      * eapply rtc_nil_step; [eapply Thread.step_break; reflexivity | econs | reflexivity].
      * left. right. left. esplits; eauto.
    + exists tr2, tr3, (stmt_continue e :: s1), [], ts1, mmts1. splits.
      * rewrite app_nil_r. exact TR.
      * exact FST.
      * eapply rtc_app; [eapply rtc_relax_base_cont; [exact REST | symmetry; apply app_nil_r] | |].
        -- eapply rtc_nil_step; [eapply Thread.step_break; reflexivity | econs | reflexivity].
        -- rewrite app_nil_r. reflexivity.
      * left. right. right. left. esplits; eauto.
Qed.

Lemma loop_rest_DR:
  forall env s0 ts0 mmts0 rmap r s_b s_body tr_h ts_c mmts_c tr_l thr_term c_pfx_term tr1 thr_term'
    (IH: DR env s_body)
    (PRE: Thread.rtc env [] tr_h (Thread.mk s0 [] ts0 mmts0)
            (Thread.mk s_body [Cont.loopcont rmap r s_b []] ts_c mmts_c))
    (CONT_TERM: thr_term.(Thread.cont) = c_pfx_term ++ [Cont.loopcont rmap r s_b []])
    (LAST: Thread.rtc env [] tr_l (Thread.mk s_body [] ts_c mmts_c)
             (Thread.mk thr_term.(Thread.stmt) c_pfx_term thr_term.(Thread.ts) thr_term.(Thread.mmts)))
    (EX2: Thread.rtc env [] tr1
            (Thread.mk s_body [Cont.loopcont rmap r s_b []] ts_c thr_term.(Thread.mmts)) thr_term'),
  DR_concl env s0 (tr_h ++ tr_l) tr1 ts0 mmts0 thr_term thr_term'.
Proof.
  intros.
  hexploit loop_iter_split; [exact EX2|].
  intros (tr_a & tr_b & s2 & c2 & ts2 & mmts2 & TR1 & FIRST & TAIL & CASES). subst tr1.
  destruct (DR_elim IH LAST FIRST)
  as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND). ss.
  assert (FST: STOP thr_term.(Thread.stmt) thr_term.(Thread.cont) ->
               thr_term.(Thread.stmt) = s_x /\ c_pfx_term = c_x /\ thr_term.(Thread.ts) = ts_x
               /\ thr_term.(Thread.mmts) = mmts2 /\ [] ~ tr_a).
  { rewrite CONT_TERM. intro STOP1. apply STOP_FST. eapply STOP_app_loop. exact STOP1. }
  destruct CASES as [STOP2 | (TR_B & THR_TERM')].
  - hexploit STOP_SND; [exact STOP2|]. intros (S2 & C2 & TS2). subst s_x c_x ts_x.
    destruct thr_term' as [s' c' ts' mmts'].
    exists (tr_h ++ tr_x ++ tr_b), s', c', ts'. splits.
    + eapply rtc_app; [exact PRE | | reflexivity].
      eapply rtc_app; [eapply rtc_lift_nil in TRACE; exact TRACE | exact TAIL | reflexivity].
    + rewrite <- ! app_assoc. apply trace_refine_app; [|apply trace_refine_eq].
      rewrite app_assoc. apply trace_refine_app; [apply trace_refine_eq | exact REFINE].
    + intro STOP1. hexploit FST; [exact STOP1|]. intros (S & C & TS & MMTS & SILENT).
      rewrite CONT_TERM, S, C in STOP1.
      hexploit stop_means_no_step; [| exact TAIL |]; [exact STOP1 |]. intros [THR TR_B].
      injection THR as S' C' TS' MMTS'. subst s' c' ts' mmts' tr_b.
      splits; [exact S | rewrite CONT_TERM, C; reflexivity | exact TS | exact MMTS |].
      rewrite app_nil_r. exact SILENT.
    + intros _. splits; ss.
  - subst tr_b thr_term'.
    exists (tr_h ++ tr_x), s_x, (c_x ++ [Cont.loopcont rmap r s_b []]), ts_x. splits.
    + eapply rtc_app; [exact PRE | eapply rtc_lift_nil in TRACE; exact TRACE | reflexivity].
    + rewrite app_nil_r. rewrite <- ! app_assoc. apply trace_refine_app; [exact REFINE | apply trace_refine_eq].
    + intro STOP1. hexploit FST; [exact STOP1|]. intros (S & C & TS & MMTS & SILENT).
      splits; [exact S | rewrite CONT_TERM, C; reflexivity | exact TS | exact MMTS |].
      rewrite app_nil_r. exact SILENT.
    + ss. intro STOP2. hexploit STOP_SND; [eapply STOP_app_loop; exact STOP2|]. intros (S2 & C2 & TS2).
      subst. splits; ss.
Qed.

Lemma loop_done_rest_DR:
  forall env s0 ts0 mmts0 rmap r s_b s_body tr_h ts_c mmts_c tr_l s_r ts_r mmts_r tr1 thr_term'
    (IH: DR env s_body)
    (PRE: Thread.rtc env [] tr_h (Thread.mk s0 [] ts0 mmts0)
            (Thread.mk s_body [Cont.loopcont rmap r s_b []] ts_c mmts_c))
    (LAST: Thread.rtc env [] tr_l (Thread.mk s_body [] ts_c mmts_c)
             (Thread.mk (stmt_break :: s_r) [] ts_r mmts_r))
    (EX2: Thread.rtc env [] tr1 (Thread.mk s_body [Cont.loopcont rmap r s_b []] ts_c mmts_r) thr_term'),
  DR_concl env s0 (tr_h ++ tr_l) tr1 ts0 mmts0
           (Thread.mk [] [] (TState.mk rmap (TState.time ts_r)) mmts_r) thr_term'.
Proof.
  intros.
  hexploit loop_iter_split; [exact EX2|].
  intros (tr_a & tr_b & s2 & c2 & ts2 & mmts2 & TR1 & FIRST & TAIL & CASES). subst tr1.
  destruct (DR_elim IH LAST FIRST)
  as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & STOP_FST & STOP_SND). ss.
  hexploit STOP_FST; [right; left; esplits; eauto|]. intros (S & C & TS & MMTS & SILENT).
  subst s_x c_x ts_x mmts2.
  assert (EX1: Thread.rtc env [] (tr_h ++ tr_l) (Thread.mk s0 [] ts0 mmts0)
                 (Thread.mk [] [] (TState.mk rmap (TState.time ts_r)) mmts_r)).
  { eapply rtc_app; [exact PRE | | reflexivity].
    eapply rtc_app; [eapply rtc_lift_nil in LAST; exact LAST | | rewrite app_nil_r; reflexivity].
    eapply rtc_nil_step; [eapply Thread.step_break; reflexivity | econs | reflexivity].
  }
  destruct CASES as [STOP2 | (TR_B & THR_TERM')].
  - hexploit STOP_SND; [exact STOP2|]. intros (S2 & C2 & TS2). subst s2 c2 ts2.
    destruct (rtc_nil_inv TAIL) as [[TR_B THR] | (tr_c & tr_d & thr_c & TR_B & STEP_B & RTC_B)]; subst.
    { apply DR_concl_snd_silent; [exact EX1 | rewrite app_nil_r; exact SILENT | reflexivity | nstop]. }
    destruct (step_break_inv STEP_B) as [TR_C (rmap' & r' & s_b' & s_c' & c'' & CONT_B & THR_C)].
    injection CONT_B as <- <- <- <- <-. subst.
    hexploit stop_means_no_step; [|exact RTC_B|]; [left; ss|]. intros [THR TR_D]. subst.
    apply DR_concl_same; [exact EX1 | rewrite ! app_nil_r; exact SILENT].
  - subst tr_b thr_term'.
    apply DR_concl_snd_silent; [exact EX1 | rewrite app_nil_r; exact SILENT | reflexivity |].
    ss. intro STOP2'. pose proof (@STOP_app_loop _ _ _ STOP2') as STOP2.
    hexploit STOP_SND; [exact STOP2|]. intros (S2 & C2 & _). subst s2 c2.
    revert STOP2'. nstop.
Qed.


Lemma sem_expr_mid_add r v rmap lab pfx
      (NMID: r <> mid)
      (MID: rmap mid = Some (Val.mid pfx)):
  sem_expr (VRegMap.add r v rmap) (expr_mid lab) = Some (Val.mid (pfx ++ [lab])).
Proof.
  unfold expr_mid. cbn [sem_expr].
  rewrite VRegMap.add_neq; [rewrite MID; ss | intro EQ; apply NMID; symmetry; exact EQ].
Qed.

Lemma loop_passed_chkpt:
  forall env envt labs' s_body lab (r: VReg) v0 ts ts_h m mmt mmts_c tr_l s_w c_w ts_w mmts_w tr0 thr0
    (OK: TypeSystem.env_ok env envt)
    (BODY: EnvType.rw_judge envt labs' s_body)
    (NIN: ~ Ensembles.In Label labs' lab)
    (NMID: r <> mid)
    (TIME: TState.time ts <= TState.time ts_h)
    (REGS_H: exists v, TState.regs ts_h = VRegMap.add r v (TState.regs ts))
    (EVAL_M: sem_expr ts_h.(TState.regs) (expr_mid lab) = Some (Val.mid m))
    (MMT: mmts_c m = mmt)
    (LT: TState.time ts_h < Mmt.time mmt)
    (REST: Thread.rtc env [] tr_l
             (Thread.mk s_body [] (TState.mk (VRegMap.add r (Mmt.val mmt) (TState.regs ts_h)) (Mmt.time mmt)) mmts_c)
             (Thread.mk s_w c_w ts_w mmts_w))
    (STEP2: Thread.step env tr0
              (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts_w) thr0),
  tr0 = []
  /\ thr0 = Thread.mk s_body [LCONT ts r lab s_body]
              (TState.mk (VRegMap.add r (Mmt.val mmt) (TState.regs ts_h)) (Mmt.time mmt)) mmts_w.
Proof.
  intros. destruct REGS_H as (v_h & REGS_H).
  hexploit sem_expr_mid; [exact EVAL_M|]. intros (pfx & MID_PFX & M). subst m.
  assert (MID_TS: TState.regs ts mid = Some (Val.mid pfx)).
  { rewrite REGS_H, VRegMap.add_neq in MID_PFX; [exact MID_PFX | intro EQ; apply NMID; symmetry; exact EQ]. }
  hexploit loop_body_mmt; [exact OK | exact BODY | exact NIN | | exact REST |].
  { ss. rewrite VRegMap.add_neq; [exact MID_PFX | intro EQ; apply NMID; symmetry; exact EQ]. }
  intro MMT_W.
  hexploit loop_head_replay;
    [exact TIME | apply sem_expr_mid_add; [exact NMID | exact MID_TS] | exists v_h; exact REGS_H | | exact STEP2 |].
  { rewrite MMT_W, MMT. exact LT. }
  intros [TR0 THR0]. rewrite MMT_W, MMT in THR0. split; ss.
Qed.

Lemma loop_iter_DR:
  forall env envt labs' s_body lab r e v0 ts mmts tr thr_term tr0 tr1 thr0 thr_term'
    (OK: TypeSystem.env_ok env envt)
    (BODY: EnvType.rw_judge envt labs' s_body)
    (NIN: ~ Ensembles.In Label labs' lab)
    (NMID: r <> mid)
    (IH: DR env s_body)
    (EVAL0: sem_expr ts.(TState.regs) e = Some v0)
    (EX1: Thread.rtc env [LCONT ts r lab s_body] tr
            (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts) thr_term)
    (STEP2: Thread.step env tr0
              (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) thr_term.(Thread.mmts)) thr0)
    (EX2: Thread.rtc env [] tr1 thr0 thr_term')
    (HEAD: (forall e0 s_r, thr_term.(Thread.stmt) <> stmt_continue e0 :: s_r) ->
           forall tr_h ts_h,
             loop_prefix env r lab s_body ts v0 mmts tr_h ts_h thr_term.(Thread.mmts) ->
             DR_concl env [stmt_loop (Some r) e (LBODY r lab s_body)] tr_h (tr0 ++ tr1) ts mmts
                      (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] ts_h thr_term.(Thread.mmts))
                      thr_term'),
  DR_concl env [stmt_loop (Some r) e (LBODY r lab s_body)] tr (tr0 ++ tr1) ts mmts thr_term thr_term'.
Proof.
  intros.
  hexploit loop_last_iter; [exact EX1|].
  intros (tr_h & tr_l & ts_h & mmts_h & c_pfx_term & TR & PFX & CONT_TERM & LAST). subst tr.
  hexploit loop_prefix_rtc; [exact EVAL0 | exact PFX |]. intros (PRE & TIME & REGS_H).
  hexploit loop_body_cases; [exact LAST|].
  intros [(TR_L & THR_L) | [(m & TR_L & THR_L) | (m & mmt & mmts_c & EVAL_M & MMT & LT & CHK & REST)]].
  - (* (1) the last iteration has not started *)
    destruct thr_term as [st ct tst mt]. ss. inv THR_L. rewrite app_nil_r.
    apply HEAD; [intros e0 s_r EQ; inv EQ | exact PFX].
  - (* (2) the last iteration is inside its checkpoint *)
    destruct thr_term as [st ct tst mt]. ss. inv THR_L. rewrite app_nil_r.
    eapply DR_peel with (thr_m := Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] ts_h mmts_h).
    { ss. nstop. }
    apply HEAD; [intros e0 s_r EQ; inv EQ | exact PFX].
  - (* (3), (4) the last iteration has passed its checkpoint *)
    hexploit loop_passed_chkpt; [exact OK | exact BODY | exact NIN | exact NMID | exact TIME | exact REGS_H
                                 | exact EVAL_M | exact MMT | exact LT | exact REST | exact STEP2 |].
    intros [TR0 THR0]. subst tr0 thr0.
    eapply loop_rest_DR; [exact IH | | exact CONT_TERM | exact REST | exact EX2].
    eapply rtc_app; [exact PRE | eapply rtc_lift_nil in CHK; exact CHK | rewrite app_nil_r; reflexivity].
Qed.

Lemma loop_head_DR:
  forall env envt labs' s_body lab r e v0 ts mmts tr_h ts_h mmts_h tr0 tr1 thr0 thr_term'
    (OK: TypeSystem.env_ok env envt)
    (BODY: EnvType.rw_judge envt labs' s_body)
    (NIN: ~ Ensembles.In Label labs' lab)
    (NMID: r <> mid)
    (IH: DR env s_body)
    (EVAL0: sem_expr ts.(TState.regs) e = Some v0)
    (PFX: loop_prefix env r lab s_body ts v0 mmts tr_h ts_h mmts_h)
    (STEP2: Thread.step env tr0
              (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts_h) thr0)
    (EX2: Thread.rtc env [] tr1 thr0 thr_term'),
  DR_concl env [stmt_loop (Some r) e (LBODY r lab s_body)] tr_h (tr0 ++ tr1) ts mmts
           (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] ts_h mmts_h) thr_term'.
Proof.
  intros.
  assert (LOOP: Thread.step env []
                  (Thread.mk [stmt_loop (Some r) e (LBODY r lab s_body)] [] ts mmts)
                  (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts)).
  { exact (@Thread.step_loop env (Some r) e (LBODY r lab s_body) [] [] ts mmts v0 EVAL0). }
  destruct PFX as [(TS_H & MMTS_H & TR_H) | (e0 & s_r & ts_r & v & ITERS & EVAL & TS_H)]; subst.
  - apply DR_concl_fst_silent; [apply trace_refine_eq | nstop |].
    eapply rtc_nil_step; [exact LOOP | eapply rtc_nil_step; [exact STEP2 | exact EX2 | reflexivity] | reflexivity].
  - eapply DR_peel with (thr_m := Thread.mk (stmt_continue e0 :: s_r) [LCONT ts r lab s_body] ts_r mmts_h).
    { nstop. }
    eapply loop_iter_DR; [exact OK | exact BODY | exact NIN | exact NMID | exact IH | exact EVAL0
                          | exact ITERS | exact STEP2 | exact EX2 |].
    intros NCONT. exfalso. eapply NCONT. reflexivity.
Qed.

Lemma loop_done_DR:
  forall env envt labs' s_body lab r e v0 ts mmts tr s_r ts_r mmts_r tr0 tr1 thr0 thr_term'
    (OK: TypeSystem.env_ok env envt)
    (BODY: EnvType.rw_judge envt labs' s_body)
    (NIN: ~ Ensembles.In Label labs' lab)
    (NMID: r <> mid)
    (IH: DR env s_body)
    (EVAL0: sem_expr ts.(TState.regs) e = Some v0)
    (EX1: Thread.rtc env [LCONT ts r lab s_body] tr
            (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts)
            (Thread.mk (stmt_break :: s_r) [LCONT ts r lab s_body] ts_r mmts_r))
    (STEP2: Thread.step env tr0
              (Thread.mk (LBODY r lab s_body) [LCONT ts r lab s_body] (LTS r v0 ts) mmts_r) thr0)
    (EX2: Thread.rtc env [] tr1 thr0 thr_term'),
  DR_concl env [stmt_loop (Some r) e (LBODY r lab s_body)] tr (tr0 ++ tr1) ts mmts
           (Thread.mk [] [] (TState.mk (TState.regs ts) (TState.time ts_r)) mmts_r) thr_term'.
Proof.
  intros.
  hexploit loop_last_iter; [exact EX1|].
  intros (tr_h & tr_l & ts_h & mmts_h & c_pfx_term & TR & PFX & CONT_TERM & LAST). subst tr. ss.
  assert (c_pfx_term = []).
  { destruct c_pfx_term as [|c0 c_pfx_term]; ss. inv CONT_TERM. destruct c_pfx_term; ss. }
  subst c_pfx_term.
  hexploit loop_prefix_rtc; [exact EVAL0 | exact PFX |]. intros (PRE & TIME & REGS_H).
  hexploit loop_body_cases; [exact LAST|].
  intros [(TR_L & THR_L) | [(m & TR_L & THR_L) | (m & mmt & mmts_c & EVAL_M & MMT & LT & CHK & REST)]];
    try by inv THR_L.
  hexploit loop_passed_chkpt; [exact OK | exact BODY | exact NIN | exact NMID | exact TIME | exact REGS_H
                               | exact EVAL_M | exact MMT | exact LT | exact REST | exact STEP2 |].
  intros [TR0 THR0]. subst tr0 thr0.
  eapply loop_done_rest_DR; [exact IH | | exact REST | exact EX2].
  eapply rtc_app; [exact PRE | eapply rtc_lift_nil in CHK; exact CHK | rewrite app_nil_r; reflexivity].
Qed.

Lemma DR_loop:
  forall env envt labs' s_body r e lab
    (OK: TypeSystem.env_ok env envt)
    (BODY: EnvType.rw_judge envt labs' s_body)
    (NIN: ~ Ensembles.In Label labs' lab)
    (NMID: r <> mid)
    (IH: DR env s_body),
  DR env [stmt_loop (Some r) e (LBODY r lab s_body)].
Proof.
  intros. apply DR_fold. intros tr tr' thr_term thr_term' ts mmts EX1 EX2.
  destruct (rtc_nil_inv EX1) as [[TR1 THR1] | (tr1 & tr1' & thr1 & TR1 & STEP1 & RTC1)]; subst.
  { apply DR_concl_fst_silent; [apply trace_refine_eq | nstop | exact EX2]. }
  destruct (rtc_nil_inv EX2) as [[TR2 THR2] | (tr2 & tr2' & thr2 & TR2 & STEP2 & RTC2)]; subst.
  { apply DR_concl_snd_silent; [exact EX1 | apply trace_refine_eq | reflexivity | nstop]. }
  destruct (step_loop_inv STEP1) as [TR1a (v1 & EVAL1 & THR1)].
  destruct (step_loop_inv STEP2) as [TR2a (v2 & EVAL2 & THR2)].
  rewrite EVAL1 in EVAL2. injection EVAL2 as <-. subst.
  destruct (rtc_nil_inv RTC2) as [[TR2 THR2] | (tr3 & tr3' & thr3 & TR3 & STEP3 & RTC3)]; subst.
  { apply DR_concl_snd_silent; [exact EX1 | apply trace_refine_eq | reflexivity | nstop]. }
  rewrite ! app_nil_l.
  hexploit (@loop_cases env [] tr1' _ _ [] (TState.regs ts) (Some r) (LBODY r lab s_body) [] RTC1);
    [reflexivity |].
  intros [ONG | (tr_a & tr_b & s_r & ts_r & mmts_r & TR & BRK & OUT)].
  - (* EX1: loop-ongoing *)
    eapply loop_iter_DR; [exact OK | exact BODY | exact NIN | exact NMID | exact IH | exact EVAL1
                          | exact ONG | exact STEP3 | exact RTC3 |].
    intros NCONT tr_h ts_h PFX.
    eapply loop_head_DR; [exact OK | exact BODY | exact NIN | exact NMID | exact IH | exact EVAL1
                          | exact PFX | exact STEP3 | exact RTC3].
  - (* EX1: loop-done *)
    hexploit stop_means_no_step; [|exact OUT|]; [left; ss|]. intros [THR TR_B]. subst.
    rewrite app_nil_r.
    eapply loop_done_DR; [exact OK | exact BODY | exact NIN | exact NMID | exact IH | exact EVAL1
                          | exact BRK | exact STEP3 | exact RTC3].
Qed.
