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
From Memento Require Import DR.

Set Implicit Arguments.

Definition rw_code (envt: EnvType.t) (s: list Stmt) : Prop :=
  Forall (fun x => exists labs, EnvType.rw_judge envt labs [x]) s.

Definition rw_frame (envt: EnvType.t) (c: Cont.t) : Prop :=
  match c with
  | Cont.loopcont _ _ s_body s_cont => rw_code envt s_body /\ rw_code envt s_cont
  | Cont.fncont _ _ s_cont => rw_code envt s_cont
  | Cont.chkptcont _ _ _ _ => False
  end.

Definition rw_thread (envt: EnvType.t) (thr: Thread.t) : Prop :=
  rw_code envt thr.(Thread.stmt) /\ Forall (rw_frame envt) thr.(Thread.cont).

Definition touch (s: list Stmt) : Prop :=
  match s with
  | stmt_chkpt _ _ _ :: _ | stmt_pcas _ _ _ _ _ :: _ => True
  | _ => False
  end.

Definition scr (thr: Thread.t) : list Stmt * list Cont.t * VRegMap.t :=
  (thr.(Thread.stmt), thr.(Thread.cont), thr.(Thread.ts).(TState.regs)).

Lemma scr_eq thr1 thr2
      (SCR: scr thr1 = scr thr2)
      (TIME: thr1.(Thread.ts).(TState.time) = thr2.(Thread.ts).(TState.time))
      (MMTS: thr1.(Thread.mmts) = thr2.(Thread.mmts)):
  thr1 = thr2.
Proof.
  destruct thr1 as [s1 c1 [r1 t1] m1], thr2 as [s2 c2 [r2 t2] m2]. unfold scr in *. ss. inv SCR. subst. ss.
Qed.

Lemma rw_code_judge envt labs s
      (RW: EnvType.rw_judge envt labs s):
  rw_code envt s.
Proof.
  eapply Forall_impl; [|apply EnvShape.rw_judge_forall; exact RW]. intros x (labs' & _ & RW'). eauto.
Qed.

Lemma loop_head_code envt r lab s
      (NMID: r <> mid)
      (RW: rw_code envt s):
  rw_code envt (stmt_chkpt r [stmt_return (expr_reg r)] (expr_mid lab) :: s).
Proof. econs; ss. eexists. apply loop_head_rw. ss. Qed.

Local Ltac shift_step :=
  match goal with
  | |- Thread.step _ _ (Thread.mk _ _ (TState.mk ?R ?T) _) _ =>
      let ts0 := fresh "ts0" in
      set (ts0 := TState.mk R T); change R with (TState.regs ts0); change T with (TState.time ts0)
  end;
  first [ eapply (@Thread.step_loop _ (Some _)); eauto; fail
        | eapply (@Thread.step_loop _ None); eauto; fail
        | econs; eauto ].

Lemma pure_step:
  forall env envt tr thr thr',
    TypeSystem.env_ok env envt ->
    rw_thread envt thr ->
    ~ touch thr.(Thread.stmt) ->
    Thread.step env tr thr thr' ->
  tr = []
  /\ thr'.(Thread.mmts) = thr.(Thread.mmts)
  /\ thr'.(Thread.ts).(TState.time) = thr.(Thread.ts).(TState.time)
  /\ rw_thread envt thr'
  /\ forall t mmts,
      Thread.step env []
        (Thread.mk thr.(Thread.stmt) thr.(Thread.cont) (TState.mk thr.(Thread.ts).(TState.regs) t) mmts)
        (Thread.mk thr'.(Thread.stmt) thr'.(Thread.cont) (TState.mk thr'.(Thread.ts).(TState.regs) t) mmts).
Proof.
  intros env envt tr thr thr' [OK_RO OK_RW] [RW RW_C] NT STEP.
  inv STEP; ss; try (exfalso; apply NT; ss; fail);
    inversion RW as [|? ? (labs & ONE) RW']; subst; apply EnvShape.rw_judge_single in ONE; ss.
  - (* assign *) splits; ss. i. shift_step.
  - (* branch *) destruct ONE as (labs_t & labs_f & RW_T & RW_F & _ & _ & _).
    splits; ss.
    + split; ss. apply Forall_app. split; ss. destruct b; eapply rw_code_judge; eauto.
    + i. shift_step.
  - (* loop *) destruct r as [r|].
    + destruct ONE as (lab & labs' & s' & S_BODY & RW_B & NIN & IN & INCL & NMID & MF). subst.
      splits; ss.
      * split; [apply loop_head_code; [ss | eapply rw_code_judge; eauto]|].
        econs; ss. split; [apply loop_head_code; [ss | eapply rw_code_judge; eauto] | ss].
      * i. shift_step.
    + destruct ONE as (E & labs' & RW_B & INCL). subst.
      splits; ss.
      * split; [eapply rw_code_judge; eauto|]. econs; ss. split; [eapply rw_code_judge; eauto | ss].
      * i. shift_step.
  - (* continue *) inversion RW_C as [|? ? FR RW_C']. subst. destruct FR as [RW_B RW_S].
    splits; ss. i. shift_step.
  - (* break *) inversion RW_C as [|? ? FR RW_C']. subst. destruct FR as [RW_B RW_S].
    splits; ss. i. shift_step.
  - (* call *) destruct ONE as (es' & lab & ES & FN & IN & NMID & MF).
    hexploit OK_RW; eauto. intros (prms' & labs' & s_f' & FIND' & RW_F & _). rewrite FIND in FIND'. inv FIND'.
    splits; ss.
    + split; [eapply rw_code_judge; eauto|]. econs; ss.
    + i. shift_step.
  - (* return *) apply Forall_app in RW_C. destruct RW_C as [_ RW_C]. inversion RW_C as [|? ? FR RW_C']. subst.
    splits; ss. i. shift_step.
  - (* chkpt-return *) apply Forall_app in RW_C. destruct RW_C as [_ RW_C]. inversion RW_C as [|? ? FR RW_C']. ss.
Qed.

Lemma pure_step_det:
  forall env envt tr1 tr2 thr1 thr2 thr1' thr2',
    rw_thread envt thr1 ->
    ~ touch thr1.(Thread.stmt) ->
    scr thr1 = scr thr2 ->
    Thread.step env tr1 thr1 thr1' ->
    Thread.step env tr2 thr2 thr2' ->
  scr thr1' = scr thr2'.
Proof.
  intros env envt tr1 tr2 [s1 c1 [rm1 t1] m1] [s2 c2 [rm2 t2] m2] thr1' thr2' [RW RW_C] NT SCR STEP1 STEP2.
  unfold scr in *. ss. inv SCR.
  inv STEP1; ss; try (exfalso; apply NT; ss; fail);
    try (inversion RW as [|? ? (labs & ONE) RW']; subst; apply EnvShape.rw_judge_single in ONE; ss; fail);
    try (apply Forall_app in RW_C; destruct RW_C as [_ RW_C]; inversion RW_C as [|? ? FR RW_C']; ss; fail);
    inv STEP2; ss; clarify.
  all: hexploit Cont.loops_base_cont_eq; [exact LOOPS | exact LOOPS0 | idtac | idtac | exact CONT | idtac].
  all: try (intro L; inv L; ss; fail).
Qed.

Lemma scr_inv thr1 thr2
      (SCR: scr thr1 = scr thr2):
  thr1.(Thread.stmt) = thr2.(Thread.stmt) /\ thr1.(Thread.cont) = thr2.(Thread.cont)
  /\ thr1.(Thread.ts).(TState.regs) = thr2.(Thread.ts).(TState.regs).
Proof. unfold scr in SCR. injection SCR as S C R. auto. Qed.

Lemma rw_thread_scr envt thr1 thr2
      (SCR: scr thr1 = scr thr2)
      (RW: rw_thread envt thr1):
  rw_thread envt thr2.
Proof. apply scr_inv in SCR. destruct SCR as (S & C & _). unfold rw_thread. rewrite <- S, <- C. ss. Qed.

Lemma pure_step_eq:
  forall env envt tr1 tr2 thr thr1 thr2,
    TypeSystem.env_ok env envt ->
    rw_thread envt thr ->
    ~ touch thr.(Thread.stmt) ->
    Thread.step env tr1 thr thr1 ->
    Thread.step env tr2 thr thr2 ->
  thr1 = thr2.
Proof.
  intros env envt tr1 tr2 thr thr1 thr2 OK RW NT STEP1 STEP2.
  hexploit pure_step; [exact OK | exact RW | exact NT | exact STEP1 |]. intros (_ & M1 & T1 & _).
  hexploit pure_step; [exact OK | exact RW | exact NT | exact STEP2 |]. intros (_ & M2 & T2 & _).
  apply scr_eq; [eapply pure_step_det; eauto | congr | congr].
Qed.

Inductive prtc (env: Env.t) (envt: EnvType.t) : Thread.t -> Thread.t -> Prop :=
| prtc_refl
    thr
  : prtc env envt thr thr
| prtc_step
    thr thr1 thr2
    (RW: rw_thread envt thr)
    (NT: ~ touch thr.(Thread.stmt))
    (STEP: Thread.step env [] thr thr1)
    (PRTC: prtc env envt thr1 thr2)
  : prtc env envt thr thr2
.

Lemma prtc_rtc:
  forall env envt thr thr',
    TypeSystem.env_ok env envt ->
    prtc env envt thr thr' ->
  Thread.rtc env [] [] thr thr'
  /\ thr'.(Thread.mmts) = thr.(Thread.mmts)
  /\ thr'.(Thread.ts).(TState.time) = thr.(Thread.ts).(TState.time).
Proof.
  intros env envt thr thr' OK PRTC. induction PRTC.
  - splits; ss. econs 1.
  - hexploit pure_step; [exact OK | exact RW | exact NT | exact STEP |]. intros (_ & MMTS & TIME & _ & _).
    destruct IHPRTC as (RTC & MMTS' & TIME'). splits.
    + eapply rtc_nil_step; [exact STEP | exact RTC | ss].
    + congr.
    + congr.
Qed.

Lemma prtc_rw:
  forall env envt thr thr',
    TypeSystem.env_ok env envt ->
    prtc env envt thr thr' ->
    rw_thread envt thr ->
  rw_thread envt thr'.
Proof.
  intros env envt thr thr' OK PRTC. induction PRTC; ss. i. apply IHPRTC.
  hexploit pure_step; [exact OK | exact RW | exact NT | exact STEP |]. intros (_ & _ & _ & RW1 & _). ss.
Qed.

Lemma prtc_trans:
  forall env envt thr1 thr2 thr3,
    prtc env envt thr1 thr2 ->
    prtc env envt thr2 thr3 ->
  prtc env envt thr1 thr3.
Proof. intros env envt thr1 thr2 thr3 P12. induction P12; ss. i. econs 2; eauto. Qed.

Lemma prtc_shift:
  forall env envt thr thr',
    TypeSystem.env_ok env envt ->
    prtc env envt thr thr' ->
  forall t mmts,
    prtc env envt
      (Thread.mk thr.(Thread.stmt) thr.(Thread.cont) (TState.mk thr.(Thread.ts).(TState.regs) t) mmts)
      (Thread.mk thr'.(Thread.stmt) thr'.(Thread.cont) (TState.mk thr'.(Thread.ts).(TState.regs) t) mmts).
Proof.
  intros env envt thr thr' OK PRTC. induction PRTC; i.
  - econs 1.
  - hexploit pure_step; [exact OK | exact RW | exact NT | exact STEP |]. intros (_ & _ & _ & _ & SHIFT).
    econs 2; [| | eapply SHIFT | eapply IHPRTC]; ss.
Qed.

Lemma prtc_lift:
  forall env envt thr thr' c_a,
    prtc env envt thr thr' ->
    Forall (rw_frame envt) c_a ->
  prtc env envt
    (Thread.mk thr.(Thread.stmt) (thr.(Thread.cont) ++ c_a) thr.(Thread.ts) thr.(Thread.mmts))
    (Thread.mk thr'.(Thread.stmt) (thr'.(Thread.cont) ++ c_a) thr'.(Thread.ts) thr'.(Thread.mmts)).
Proof.
  intros env envt thr thr' c_a PRTC RW_A. induction PRTC.
  - econs 1.
  - econs 2; [| | | exact IHPRTC].
    + destruct RW as [RW RW_C]. split; ss. apply Forall_app. split; ss.
    + ss.
    + destruct thr as [s c ts mmts], thr1 as [s1 c1 ts1 mmts1]. ss. apply step_lift. ss.
Qed.

Lemma prtc_det:
  forall env envt thr thr1,
    TypeSystem.env_ok env envt ->
    prtc env envt thr thr1 ->
  forall thr2,
    prtc env envt thr thr2 ->
  prtc env envt thr1 thr2 \/ prtc env envt thr2 thr1.
Proof.
  intros env envt thr thr1 OK PRTC. induction PRTC; intros thr3 PRTC3.
  - left. ss.
  - inversion PRTC3 as [thr' | thr' thr1' thr3' RW' NT' STEP' PRTC']; subst.
    + right. econs 2; eauto.
    + hexploit (@pure_step_eq env envt [] [] thr thr1 thr1'); eauto. intro EQ. subst thr1'. eauto.
Qed.

Lemma prtc_touch_nstop:
  forall env envt thr thr',
    prtc env envt thr thr' ->
    touch thr'.(Thread.stmt) ->
  ~ STOP thr.(Thread.stmt) thr.(Thread.cont).
Proof.
  intros env envt thr thr' PRTC TOUCH STOP1.
  inversion PRTC as [thr0 | thr0 thr1 thr2 RW NT STEP PRTC']; subst.
  - destruct thr' as [s c ts mmts]. ss. unfold STOP in STOP1. des; subst; ss.
  - destruct thr as [s c ts mmts], thr1 as [s1 c1 ts1 mmts1]. eapply stop_no_step; eauto.
Qed.

Lemma follow:
  forall env envt thr_a thr_z,
    TypeSystem.env_ok env envt ->
    prtc env envt thr_a thr_z ->
  forall tr thr_b thr_b',
    Thread.rtc env [] tr thr_b thr_b' ->
    scr thr_a = scr thr_b ->
  (exists thr_m,
      prtc env envt thr_a thr_m /\ prtc env envt thr_m thr_z /\ scr thr_m = scr thr_b'
      /\ tr = [] /\ thr_b'.(Thread.ts).(TState.time) = thr_b.(Thread.ts).(TState.time)
      /\ thr_b'.(Thread.mmts) = thr_b.(Thread.mmts))
  \/ (exists thr_bz,
      Thread.rtc env [] [] thr_b thr_bz /\ scr thr_z = scr thr_bz
      /\ thr_bz.(Thread.ts).(TState.time) = thr_b.(Thread.ts).(TState.time)
      /\ thr_bz.(Thread.mmts) = thr_b.(Thread.mmts)
      /\ Thread.rtc env [] tr thr_bz thr_b').
Proof.
  intros env envt thr_a thr_z OK PRTC. induction PRTC; intros tr thr_b thr_b' RTC SCR.
  - right. exists thr_b. splits; ss. econs 1.
  - destruct (rtc_nil_inv RTC) as [[TR THR] | (tr0 & tr1 & thr_b0 & TR & STEP_B & RTC_B)]; subst.
    + left. exists thr. splits; ss; [econs 1 | econs 2; eauto].
    + assert (NT_B: ~ touch thr_b.(Thread.stmt)).
      { apply scr_inv in SCR. destruct SCR as (S & _ & _). rewrite <- S. ss. }
      hexploit pure_step; [exact OK | eapply rw_thread_scr; eauto | exact NT_B | exact STEP_B |].
      intros (TR0 & MMTS0 & TIME0 & _ & _). subst tr0.
      hexploit pure_step_det; [exact RW | exact NT | exact SCR | exact STEP | exact STEP_B |]. intro SCR1.
      hexploit IHPRTC; [exact RTC_B | exact SCR1 |].
      intros [(thr_m & P1 & P2 & SCR_M & TR1 & TIME1 & MMTS1) | (thr_bz & RTC_Z & SCR_Z & TIME_Z & MMTS_Z & REST)].
      * left. exists thr_m. splits; eauto; [econs 2; eauto | congr | congr].
      * right. exists thr_bz. splits; eauto; [eapply rtc_nil_step; [exact STEP_B | exact RTC_Z | ss] | congr | congr].
Qed.

Lemma mmt_time_gt_step:
  forall env tr thr thr' m T,
    Thread.step env tr thr thr' ->
    T <= thr.(Thread.ts).(TState.time) ->
    T < (thr.(Thread.mmts) m).(Mmt.time) ->
  T < (thr'.(Thread.mmts) m).(Mmt.time).
Proof.
  intros env tr thr thr' m T STEP LE LT.
  inv STEP; ss; try lia; rewrite fun_add_spec; destruct (m == m0); ss; lia.
Qed.

Lemma mmt_time_gt:
  forall env c tr thr thr' m T,
    Thread.rtc env c tr thr thr' ->
    T <= thr.(Thread.ts).(TState.time) ->
    T < (thr.(Thread.mmts) m).(Mmt.time) ->
  T < (thr'.(Thread.mmts) m).(Mmt.time).
Proof.
  intros env c tr thr thr' m T RTC. induction RTC; ss. i. inv ONE.
  apply IHRTC.
  - hexploit Thread.step_time; eauto. lia.
  - eapply mmt_time_gt_step; eauto.
Qed.

Definition touch_mid (s: list Stmt) (e: Expr) : Prop :=
  match s with
  | stmt_chkpt _ _ e_mid :: _ | stmt_pcas _ _ _ _ e_mid :: _ => e = e_mid
  | _ => False
  end.

Lemma touch_mid_touch s e
      (TM: touch_mid s e):
  touch s.
Proof. destruct s as [|x s]; ss. destruct x; ss. Qed.

Lemma touch_nstop s c
      (TOUCH: touch s):
  ~ STOP s c.
Proof. intro STOP1. unfold STOP in STOP1. des; subst; ss. Qed.

Lemma touch_cases:
  forall env envt tr thr thr',
    TypeSystem.env_ok env envt ->
    Thread.rtc env [] tr thr thr' ->
    rw_thread envt thr ->
  (tr = [] /\ prtc env envt thr thr')
  \/ ([] ~ tr /\ thr'.(Thread.mmts) = thr.(Thread.mmts)
      /\ exists c_pfx rmap r s m c_rest, thr'.(Thread.cont) = c_pfx ++ Cont.chkptcont rmap r s m :: c_rest)
  \/ (exists thr_z e m,
        prtc env envt thr thr_z
        /\ touch_mid thr_z.(Thread.stmt) e
        /\ sem_expr thr_z.(Thread.ts).(TState.regs) e = Some (Val.mid m)
        /\ thr.(Thread.ts).(TState.time) < (thr'.(Thread.mmts) m).(Mmt.time)).
Proof.
  intros env envt tr thr thr' OK RTC. induction RTC; intros RW.
  { left. split; ss. econs 1. }
  subst. inversion ONE as [c_p STEP BASE]. clear ONE BASE.
  destruct (classic (touch thr.(Thread.stmt))) as [TOUCH | NT].
  - right. destruct thr as [s c ts mmts]. ss.
    destruct s as [|x s]; ss. destruct x; ss.
    + (* chkpt *)
      rename r into r_c, s0 into s_c.
      destruct (step_chkpt_inv STEP) as [TR0 (m & EVAL & [(LE & THR0) | (LT & THR0)])]; subst.
      * (* chkpt-call *)
        destruct RW as [RW _]. inversion RW as [|? ? (labs & ONE) _]. subst.
        apply EnvShape.rw_judge_single in ONE. destruct ONE as (lab & E_MID & IN & RO & NMID & MF).
        hexploit (@chkpt_fn_cases env [] tr1 _ _ [] (Cont.chkptcont (TState.regs ts) r_c s m) c RTC);
          [ss | intro L; inv L; ss |].
        intros [(c_pfx & CONT & BODY) | (tr_b & tr_r & s_r & c_r & ts_r & mmts_r & e_r & TR & BODY & RET & LOOPS)].
        { left. ss. hexploit ro_run; [exact OK | exact RO | exact BODY |]. intros (SILENT & MMTS & _).
          splits; ss. esplits. exact CONT. }
        right. ss. hexploit ro_run; [exact OK | exact RO | exact BODY |]. intros (_ & MMTS & TIME). subst mmts_r.
        destruct (tc_nil_inv RET) as (tr_c & tr_d & thr_c & TR_R & STEP_R & RTC_R).
        hexploit step_return_inv; [exact STEP_R | exact LOOPS | intro L; inv L; ss |].
        intros [_ (v & _ & t & LT & THR_C)]. subst thr_c.
        exists (Thread.mk (stmt_chkpt r_c s_c e_mid :: s) c ts mmts), e_mid, m. splits; ss; [econs 1|].
        eapply mmt_time_gt; [exact RTC_R | ss; lia | ss; rewrite fun_add_spec_eq; ss; lia].
      * (* chkpt-replay *)
        right. exists (Thread.mk (stmt_chkpt r_c s_c e_mid :: s) c ts mmts), e_mid, m. splits; ss; [econs 1|].
        eapply mmt_time_gt; [exact RTC | ss; lia | ss].
    + (* pcas *)
      destruct (step_pcas_inv STEP) as [(m & v_r & t & EVAL & LE & LT & THR0) | (m & EVAL & LT & TR0 & THR0)]; subst.
      * right. exists (Thread.mk (stmt_pcas r e_loc e_old e_new e_mid :: s) c ts mmts), e_mid, m.
        splits; ss; [econs 1|].
        eapply mmt_time_gt; [exact RTC | ss; lia | ss; rewrite fun_add_spec_eq; ss].
      * right. exists (Thread.mk (stmt_pcas r e_loc e_old e_new e_mid :: s) c ts mmts), e_mid, m.
        splits; ss; [econs 1|].
        eapply mmt_time_gt; [exact RTC | ss; lia | ss].
  - hexploit pure_step; [exact OK | exact RW | exact NT | exact STEP |]. intros (TR0 & MMTS0 & TIME0 & RW1 & _).
    subst tr0. hexploit IHRTC; [exact RW1 |].
    intros [(TR1 & P) | [(SILENT & MMTS & C) | (thr_z & e & m & P & TM & EVAL & LT)]].
    + left. subst. split; ss. econs 2; eauto.
    + right. left. splits; ss. congr.
    + right. right. exists thr_z, e, m. splits; eauto; [econs 2; eauto | rewrite <- TIME0; exact LT].
Qed.

Local Notation LC rmap s_b := (Cont.loopcont rmap None s_b []) (only parsing).

Lemma rw_frame_lc envt rmap s_b
      (RW_B: rw_code envt s_b):
  Forall (rw_frame envt) [LC rmap s_b].
Proof. econs; [split; [ss | econs] | econs]. Qed.

Lemma touch_replay:
  forall env tr s c regs t mmts e m thr',
    touch_mid s e ->
    sem_expr regs e = Some (Val.mid m) ->
    t < (mmts m).(Mmt.time) ->
    Thread.step env tr (Thread.mk s c (TState.mk regs t) mmts) thr' ->
  tr = []
  /\ forall t', t' < (mmts m).(Mmt.time) ->
      Thread.step env [] (Thread.mk s c (TState.mk regs t') mmts) thr'.
Proof.
  intros env tr s c regs t mmts e m thr' TM EVAL LT STEP.
  destruct s as [|x s]; ss. destruct x; ss; subst.
  - hexploit chkpt_replay_forced; [exact STEP | exact EVAL | exact LT |]. intros [TR THR]. subst.
    split; ss. intros t' LT'.
    exact (@Thread.step_chkpt_replay env r s0 e_mid s c (TState.mk regs t') mmts m EVAL LT').
  - hexploit pcas_replay_forced; [exact STEP | exact EVAL | exact LT |]. intros [TR THR]. subst.
    split; ss. intros t' LT'.
    exact (@Thread.step_pcas_replay env r e_loc e_old e_new e_mid s c (TState.mk regs t') mmts m EVAL LT').
Qed.

Definition simple_prefix (env: Env.t) (s_b: list Stmt) (rmap: VRegMap.t) (t0: nat) (mmts: Mmts.t)
           (tr_h: list Event.t) (t_h: nat) (mmts_h: Mmts.t) : Prop :=
  (t_h = t0 /\ mmts_h = mmts /\ tr_h = [])
  \/ (exists e s_r ts_r v,
        Thread.rtc env [LC rmap s_b] tr_h
          (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts)
          (Thread.mk (stmt_continue e :: s_r) [LC rmap s_b] ts_r mmts_h)
        /\ sem_expr ts_r.(TState.regs) e = Some v /\ t_h = ts_r.(TState.time)).

Lemma simple_prefix_rtc:
  forall env s_b rmap t0 mmts tr_h t_h mmts_h,
    simple_prefix env s_b rmap t0 mmts tr_h t_h mmts_h ->
  Thread.rtc env [] tr_h
    (Thread.mk [stmt_loop None expr_unit s_b] [] (TState.mk rmap t0) mmts)
    (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t_h) mmts_h)
  /\ t0 <= t_h.
Proof.
  intros env s_b rmap t0 mmts tr_h t_h mmts_h PFX.
  assert (LOOP: Thread.step env []
                  (Thread.mk [stmt_loop None expr_unit s_b] [] (TState.mk rmap t0) mmts)
                  (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts)).
  { exact (@Thread.step_loop env None expr_unit s_b [] [] (TState.mk rmap t0) mmts Val.unit eq_refl). }
  destruct PFX as [(T & M & TR) | (e & s_r & ts_r & v & ITERS & EVAL & T)]; subst.
  - split; [eapply rtc_nil_step; [exact LOOP | econs | ss] | ss].
  - hexploit Thread.step_time_mon; [exact ITERS|]. ss. intro TIME. split; [|ss].
    eapply rtc_nil_step; [exact LOOP | | ss].
    eapply rtc_app; [eapply rtc_relax_base_cont; [exact ITERS | symmetry; apply app_nil_r] | |].
    + eapply rtc_nil_step; [| econs | ss].
      exact (@Thread.step_continue env e s_r [LC rmap s_b] ts_r mmts_h v rmap None s_b [] [] EVAL eq_refl).
    + rewrite app_nil_r. ss.
Qed.

Lemma simple_last_iter:
  forall env s_b rmap t0 mmts tr thr_term,
    Thread.rtc env [LC rmap s_b] tr (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts) thr_term ->
  exists tr_h tr_l t_h mmts_h c_pfx_term,
    tr = tr_h ++ tr_l
    /\ simple_prefix env s_b rmap t0 mmts tr_h t_h mmts_h
    /\ thr_term.(Thread.cont) = c_pfx_term ++ [LC rmap s_b]
    /\ Thread.rtc env [] tr_l (Thread.mk s_b [] (TState.mk rmap t_h) mmts_h)
         (Thread.mk thr_term.(Thread.stmt) c_pfx_term thr_term.(Thread.ts) thr_term.(Thread.mmts)).
Proof.
  intros env s_b rmap t0 mmts tr thr_term RTC.
  hexploit (@last_loop_iter env tr _ _ [] rmap None s_b RTC); [reflexivity |].
  intros (tr_h & tr_l & s1 & c1 & ts1 & mmts1 & c_pfx_term & TR & LAST & CONT & ITER).
  destruct LAST as [(S1 & C1 & TS1 & MMTS1 & TR_H) | (e & s_r & ts_r & v & ITERS & EVAL & S1 & C1 & TS1)];
    subst; ss.
  - exists [], tr_l, t0, mmts, c_pfx_term. splits; ss. left. splits; ss.
  - exists tr_h, tr_l, (TState.time ts_r), mmts1, c_pfx_term. splits; ss. right. esplits; eauto.
Qed.

Lemma simple_shift:
  forall env envt s_b rmap t0 t_k mmts_k thr_z e m mmts2 tr2 thr_term'
    (OK: TypeSystem.env_ok env envt)
    (RW_B: rw_code envt s_b)
    (Z: prtc env envt (Thread.mk s_b [] (TState.mk rmap t_k) mmts_k) thr_z)
    (TM: touch_mid thr_z.(Thread.stmt) e)
    (EVAL: sem_expr thr_z.(Thread.ts).(TState.regs) e = Some (Val.mid m))
    (TIME: t0 <= t_k)
    (LT: t_k < (mmts2 m).(Mmt.time))
    (EX2: Thread.rtc env [] tr2 (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts2) thr_term'),
  (tr2 = [] /\ thr_term'.(Thread.mmts) = mmts2 /\ ~ STOP thr_term'.(Thread.stmt) thr_term'.(Thread.cont))
  \/ Thread.rtc env [] tr2 (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t_k) mmts2) thr_term'.
Proof.
  intros.
  hexploit prtc_lift; [exact Z | apply rw_frame_lc; exact RW_B |]. ss. intro ZL.
  pose proof (prtc_shift OK ZL t0 mmts2) as Z0. pose proof (prtc_shift OK ZL t_k mmts2) as ZK. ss.
  hexploit follow; [exact OK | exact Z0 | exact EX2 | reflexivity |].
  intros [(thr_m & P1 & P2 & SCR & TR & TIME' & MMTS') | (thr_bz & RTC_Z & SCR & TIME' & MMTS' & REST)].
  - left. splits; ss.
    apply scr_inv in SCR. destruct SCR as (S & C & _). rewrite <- S, <- C.
    eapply prtc_touch_nstop; [exact P2 | ss; eapply touch_mid_touch; eauto].
  - assert (BZ: thr_bz = Thread.mk thr_z.(Thread.stmt) (thr_z.(Thread.cont) ++ [LC rmap s_b])
                                   (TState.mk thr_z.(Thread.ts).(TState.regs) t0) mmts2).
    { symmetry. apply scr_eq; ss. }
    subst thr_bz.
    destruct (rtc_nil_inv REST) as [[TR THR] | (tr0 & tr1 & thr0 & TR & STEP & RTC)]; subst.
    + left. splits; ss. apply touch_nstop. eapply touch_mid_touch; eauto.
    + hexploit (@touch_replay env tr0 thr_z.(Thread.stmt) (thr_z.(Thread.cont) ++ [LC rmap s_b])
                                thr_z.(Thread.ts).(TState.regs) t0 mmts2 e m thr0 TM EVAL); [lia | exact STEP |].
      intros [TR0 SHIFT]. subst tr0.
      right. eapply rtc_app; [apply (proj1 (prtc_rtc OK ZK)) | | ss].
      eapply rtc_nil_step; [apply SHIFT; lia | exact RTC | ss].
Qed.

Lemma simple_glue:
  forall env envt s_b rmap t0 mmts tr_h t_k mmts_k tr_l thr_term c_pfx_term thr_z e m tr2 thr_term'
    (OK: TypeSystem.env_ok env envt)
    (RW_B: rw_code envt s_b)
    (IH: DR env s_b)
    (PRE: Thread.rtc env [] tr_h (Thread.mk [stmt_loop None expr_unit s_b] [] (TState.mk rmap t0) mmts)
            (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t_k) mmts_k))
    (TIME: t0 <= t_k)
    (CONT_TERM: thr_term.(Thread.cont) = c_pfx_term ++ [LC rmap s_b])
    (LAST: Thread.rtc env [] tr_l (Thread.mk s_b [] (TState.mk rmap t_k) mmts_k)
             (Thread.mk thr_term.(Thread.stmt) c_pfx_term thr_term.(Thread.ts) thr_term.(Thread.mmts)))
    (Z: prtc env envt (Thread.mk s_b [] (TState.mk rmap t_k) mmts_k) thr_z)
    (TM: touch_mid thr_z.(Thread.stmt) e)
    (EVAL: sem_expr thr_z.(Thread.ts).(TState.regs) e = Some (Val.mid m))
    (LT: t_k < (thr_term.(Thread.mmts) m).(Mmt.time))
    (EX2: Thread.rtc env [] tr2 (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) thr_term.(Thread.mmts)) thr_term'),
  DR_concl env [stmt_loop None expr_unit s_b] (tr_h ++ tr_l) tr2 (TState.mk rmap t0) mmts thr_term thr_term'.
Proof.
  intros.
  hexploit simple_shift;
    [exact OK | exact RW_B | exact Z | exact TM | exact EVAL | exact TIME | exact LT | exact EX2 |].
  intros [(TR2 & MMTS2 & NSTOP2) | EX2'].
  - subst tr2. apply DR_concl_snd_silent; [| apply trace_refine_eq | exact MMTS2 | exact NSTOP2].
    eapply rtc_app; [exact PRE | | reflexivity].
    destruct thr_term as [st ct tst mt]. ss. subst ct.
    eapply rtc_lift_nil in LAST. exact LAST.
  - eapply loop_rest_DR; [exact IH | exact PRE | exact CONT_TERM | exact LAST | exact EX2'].
Qed.

Lemma simple_glue_done:
  forall env envt s_b rmap t0 mmts tr_h t_k mmts_k tr_l s_r ts_r mmts_r thr_z e m tr2 thr_term'
    (OK: TypeSystem.env_ok env envt)
    (RW_B: rw_code envt s_b)
    (IH: DR env s_b)
    (PRE: Thread.rtc env [] tr_h (Thread.mk [stmt_loop None expr_unit s_b] [] (TState.mk rmap t0) mmts)
            (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t_k) mmts_k))
    (TIME: t0 <= t_k)
    (LAST: Thread.rtc env [] tr_l (Thread.mk s_b [] (TState.mk rmap t_k) mmts_k)
             (Thread.mk (stmt_break :: s_r) [] ts_r mmts_r))
    (Z: prtc env envt (Thread.mk s_b [] (TState.mk rmap t_k) mmts_k) thr_z)
    (TM: touch_mid thr_z.(Thread.stmt) e)
    (EVAL: sem_expr thr_z.(Thread.ts).(TState.regs) e = Some (Val.mid m))
    (LT: t_k < (mmts_r m).(Mmt.time))
    (EX2: Thread.rtc env [] tr2 (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts_r) thr_term'),
  DR_concl env [stmt_loop None expr_unit s_b] (tr_h ++ tr_l) tr2 (TState.mk rmap t0) mmts
           (Thread.mk [] [] (TState.mk rmap (TState.time ts_r)) mmts_r) thr_term'.
Proof.
  intros.
  hexploit simple_shift;
    [exact OK | exact RW_B | exact Z | exact TM | exact EVAL | exact TIME | exact LT | exact EX2 |].
  intros [(TR2 & MMTS2 & NSTOP2) | EX2'].
  - subst tr2. apply DR_concl_snd_silent; [| apply trace_refine_eq | exact MMTS2 | exact NSTOP2].
    eapply rtc_app; [exact PRE | | reflexivity].
    eapply rtc_app; [eapply rtc_lift_nil in LAST; exact LAST | | rewrite app_nil_r; reflexivity].
    eapply rtc_nil_step; [eapply Thread.step_break; reflexivity | econs | reflexivity].
  - eapply loop_done_rest_DR; [exact IH | exact PRE | exact LAST | exact EX2'].
Qed.

Lemma DR_concl_tail:
  forall env s tr_a tr_b tr' ts mmts thr_v thr_term thr_term',
    DR_concl env s tr_a tr' ts mmts thr_v thr_term' ->
    [] ~ tr_b ->
    ~ STOP thr_term.(Thread.stmt) thr_term.(Thread.cont) ->
  DR_concl env s (tr_a ++ tr_b) tr' ts mmts thr_term thr_term'.
Proof.
  unfold DR_concl. intros. des. esplits; eauto.
  - rewrite <- app_assoc. apply trace_refine_nil_ins; ss.
  - i. exfalso. eauto.
Qed.

Lemma prtc_inv:
  forall env envt thr thr',
    prtc env envt thr thr' ->
  thr = thr'
  \/ exists thr1, rw_thread envt thr /\ ~ touch thr.(Thread.stmt)
            /\ Thread.step env [] thr thr1 /\ prtc env envt thr1 thr'.
Proof. intros env envt thr thr' P. inversion P; subst; eauto 10. Qed.

Lemma prtc_step_nstop:
  forall env envt tr thr thr' thr1,
    prtc env envt thr thr' ->
    Thread.step env tr thr' thr1 ->
  ~ STOP thr.(Thread.stmt) thr.(Thread.cont).
Proof.
  intros env envt tr thr thr' thr1 P STEP STOP1.
  destruct (prtc_inv P) as [EQ | (thr2 & _ & _ & STEP2 & _)].
  - subst. destruct thr' as [s c ts mmts], thr1 as [s1 c1 ts1 mmts1]. eapply stop_no_step; eauto.
  - destruct thr as [s c ts mmts], thr2 as [s2 c2 ts2 mmts2]. eapply stop_no_step; eauto.
Qed.

Lemma STOP_mid_nonloop s c1 x c2
      (STOP1: STOP s (c1 ++ x :: c2))
      (NLOOP: ~ Cont.Loops [x]):
  False.
Proof.
  destruct STOP1 as [(_ & C) | [(s_rem & _ & C) | [(s_rem & e & _ & C) | (s_rem & e & S & LOOPS)]]];
    try by destruct c1; ss.
  apply Cont.loops_app_distr in LOOPS. destruct LOOPS as [_ LOOPS]. inv LOOPS. apply NLOOP. econs; [ss | econs].
Qed.

Lemma pure_cycle:
  forall env envt thr_h thr_1,
    TypeSystem.env_ok env envt ->
    rw_thread envt thr_h ->
    ~ touch thr_h.(Thread.stmt) ->
    Thread.step env [] thr_h thr_1 ->
    prtc env envt thr_1 thr_h ->
  forall tr thr thr',
    Thread.rtc env [] tr thr thr' ->
    prtc env envt thr thr_h ->
  tr = [] /\ prtc env envt thr' thr_h.
Proof.
  intros env envt thr_h thr_1 OK RW_H NT_H STEP_H CYC tr thr thr' RTC. induction RTC; intros P.
  { split; ss. }
  subst. inversion ONE as [c_p STEP _]. clear ONE.
  assert (NEXT: exists thr_n, Thread.step env [] thr thr_n /\ prtc env envt thr_n thr_h
                         /\ rw_thread envt thr /\ ~ touch thr.(Thread.stmt)).
  { destruct (prtc_inv P) as [EQ | (thr1' & RW' & NT' & STEP' & P')].
    - subst. exists thr_1. splits; ss.
    - exists thr1'. splits; ss. }
  destruct NEXT as (thr_n & STEP_N & P_N & RW_T & NT_T).
  hexploit (@pure_step_eq env envt tr0 [] thr thr0 thr_n); eauto. intro EQ. subst thr_n.
  hexploit pure_step; [exact OK | exact RW_T | exact NT_T | exact STEP |]. intros (TR0 & _). subst tr0.
  exact (IHRTC P_N).
Qed.

Lemma simple_cycle:
  forall env envt s_b rmap t_h mmts_h e s_r ts_r mmts_c v t0 mmts,
    TypeSystem.env_ok env envt ->
    rw_code envt s_b ->
    prtc env envt (Thread.mk s_b [] (TState.mk rmap t_h) mmts_h)
         (Thread.mk (stmt_continue e :: s_r) [] ts_r mmts_c) ->
    sem_expr ts_r.(TState.regs) e = Some v ->
  exists thr_1,
    rw_thread envt (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts)
    /\ ~ touch s_b
    /\ Thread.step env [] (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts) thr_1
    /\ prtc env envt thr_1 (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts).
Proof.
  intros env envt s_b rmap t_h mmts_h e s_r ts_r mmts_c v t0 mmts OK RW_B P EVAL.
  hexploit prtc_lift; [exact P | apply rw_frame_lc; exact RW_B |]. ss. intro PL.
  pose proof (prtc_shift OK PL t0 mmts) as P0. ss.
  assert (RW_H: rw_thread envt (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts)).
  { split; [ss | apply rw_frame_lc; ss]. }
  assert (STEP_C: Thread.step env []
                    (Thread.mk (stmt_continue e :: s_r) [LC rmap s_b] (TState.mk ts_r.(TState.regs) t0) mmts)
                    (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts)).
  { exact (@Thread.step_continue env e s_r [LC rmap s_b] (TState.mk ts_r.(TState.regs) t0) mmts v rmap None s_b [] []
                                 EVAL eq_refl). }
  assert (RW_C: rw_thread envt
                  (Thread.mk (stmt_continue e :: s_r) [LC rmap s_b] (TState.mk ts_r.(TState.regs) t0) mmts)).
  { eapply prtc_rw; eauto. }
  destruct (prtc_inv P0) as [EQ | (thr1 & _ & NT1 & STEP1 & P1)].
  - injection EQ as S_B R. rewrite S_B in *.
    exists (Thread.mk (stmt_continue e :: s_r) [LC rmap (stmt_continue e :: s_r)] (TState.mk rmap t0) mmts).
    splits; ss; [|econs 1]. rewrite <- R in STEP_C. exact STEP_C.
  - exists thr1. splits; ss.
    eapply prtc_trans; [exact P1 | econs 2; [exact RW_C | ss | exact STEP_C | econs 1]].
Qed.

Lemma simple_nstop:
  forall env envt s_b rmap t_h mmts_h thr_end t_k mmts_k thr_z e,
    TypeSystem.env_ok env envt ->
    prtc env envt (Thread.mk s_b [] (TState.mk rmap t_h) mmts_h) thr_end ->
    prtc env envt (Thread.mk s_b [] (TState.mk rmap t_k) mmts_k) thr_z ->
    touch_mid thr_z.(Thread.stmt) e ->
  ~ STOP thr_end.(Thread.stmt) thr_end.(Thread.cont).
Proof.
  intros env envt s_b rmap t_h mmts_h thr_end t_k mmts_k thr_z e OK P_END P_Z TM.
  pose proof (prtc_shift OK P_Z t_h mmts_h) as P_Z'. ss.
  hexploit prtc_det; [exact OK | exact P_END | exact P_Z' |]. intros [P | P].
  - eapply prtc_touch_nstop; [exact P | ss; eapply touch_mid_touch; eauto].
  - destruct (prtc_inv P) as [EQ | (thr1 & _ & NT' & _ & _)].
    + rewrite <- EQ. ss. apply touch_nstop. eapply touch_mid_touch; eauto.
    + exfalso. apply NT'. ss. eapply touch_mid_touch; eauto.
Qed.

Lemma simple_pure_DR:
  forall env envt s_b rmap t0 mmts thr_term tr2 thr_term'
    (OK: TypeSystem.env_ok env envt)
    (P1: prtc env envt (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts) thr_term)
    (EX1: Thread.rtc env [] [] (Thread.mk [stmt_loop None expr_unit s_b] [] (TState.mk rmap t0) mmts) thr_term)
    (EX2: Thread.rtc env [] tr2
            (Thread.mk [stmt_loop None expr_unit s_b] [] (TState.mk rmap t0) thr_term.(Thread.mmts)) thr_term')
    (RTC2: Thread.rtc env [] tr2
             (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) thr_term.(Thread.mmts)) thr_term'),
  DR_concl env [stmt_loop None expr_unit s_b] [] tr2 (TState.mk rmap t0) mmts thr_term thr_term'.
Proof.
  intros.
  hexploit prtc_rtc; [exact OK | exact P1 |]. intros (_ & MMTS1 & TIME1). ss.
  rewrite MMTS1 in EX2, RTC2.
  destruct (classic (STOP thr_term.(Thread.stmt) thr_term.(Thread.cont))) as [STOP1 | NSTOP1].
  2: { apply DR_concl_fst_silent; [apply trace_refine_eq | exact NSTOP1 | exact EX2]. }
  assert (SAME: forall thr, scr thr_term = scr thr -> thr.(Thread.ts).(TState.time) = t0 ->
                       thr.(Thread.mmts) = mmts -> thr = thr_term).
  { i. apply scr_eq; ss; congr. }
  hexploit follow; [exact OK | exact P1 | exact RTC2 | reflexivity |].
  intros [(thr_m & PA & PB & SCR & TR & TIME' & MMTS') | (thr_bz & RTC_Z & SCR & TIME' & MMTS' & REST)].
  - subst tr2. destruct (prtc_inv PB) as [EQ | (thr1 & _ & _ & STEP' & _)].
    + subst thr_m. hexploit (SAME thr_term'); ss. intro EQ. subst.
      apply DR_concl_same; [exact EX1 | apply trace_refine_eq].
    + apply DR_concl_snd_silent; [exact EX1 | apply trace_refine_eq | rewrite MMTS', MMTS1; ss |].
      apply scr_inv in SCR. destruct SCR as (S & C & _). rewrite <- S, <- C.
      intro STOP2. destruct thr_m as [s c ts mmts0], thr1 as [s1 c1 ts1 mmts1]. eapply stop_no_step; eauto.
  - hexploit (SAME thr_bz); ss. intro EQ. subst thr_bz.
    hexploit stop_means_no_step; [exact STOP1 | exact REST |]. intros [EQ TR]. subst.
    apply DR_concl_same; [exact EX1 | apply trace_refine_eq].
Qed.

Lemma simple_second:
  forall env envt s_b rmap t0 mmts tr_h e0 s_r ts_r v mmts_h tr_l thr_term tr2 thr_term'
    (OK: TypeSystem.env_ok env envt)
    (RW_B: rw_code envt s_b)
    (IH: DR env s_b)
    (PRE_N: Thread.rtc env [LC rmap s_b] tr_h
              (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts)
              (Thread.mk (stmt_continue e0 :: s_r) [LC rmap s_b] ts_r mmts_h))
    (EVAL_N: sem_expr ts_r.(TState.regs) e0 = Some v)
    (RTC1: Thread.rtc env [] (tr_h ++ tr_l) (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts) thr_term)
    (SILENT: [] ~ tr_l)
    (MMTS: thr_term.(Thread.mmts) = mmts_h)
    (NSTOP_IF: forall t_k mmts_k thr_z e,
        prtc env envt (Thread.mk s_b [] (TState.mk rmap t_k) mmts_k) thr_z ->
        touch_mid thr_z.(Thread.stmt) e ->
        ~ STOP thr_term.(Thread.stmt) thr_term.(Thread.cont))
    (EX2: Thread.rtc env [] tr2
            (Thread.mk [stmt_loop None expr_unit s_b] [] (TState.mk rmap t0) thr_term.(Thread.mmts)) thr_term')
    (RTC2: Thread.rtc env [] tr2
             (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) thr_term.(Thread.mmts)) thr_term'),
  DR_concl env [stmt_loop None expr_unit s_b] (tr_h ++ tr_l) tr2 (TState.mk rmap t0) mmts thr_term thr_term'.
Proof.
  intros.
  hexploit simple_last_iter; [exact PRE_N |].
  intros (tr_h2 & tr_l2 & t_h2 & mmts_h2 & c_pfx2 & TR2 & PFX2 & CONT2 & LAST2). ss.
  assert (c_pfx2 = []).
  { destruct c_pfx2 as [|x c_pfx2]; ss. inv CONT2. destruct c_pfx2; ss. }
  subst c_pfx2 tr_h.
  hexploit touch_cases; [exact OK | exact LAST2 | split; [ss | econs] |].
  intros [(TR_L2 & P2) | [(_ & _ & C2) | (thr_z & e & m & Z & TM & EVAL & LT)]].
  - (* the second-to-last iteration closes a pure cycle *)
    hexploit simple_cycle; [exact OK | exact RW_B | exact P2 | exact EVAL_N |].
    intros (thr_1 & RW_H & NT_H & STEP_H & CYC).
    hexploit pure_cycle; [exact OK | exact RW_H | exact NT_H | exact STEP_H | exact CYC | exact RTC1 | econs 1 |].
    intros [TR1 P_T].
    hexploit prtc_rtc; [exact OK | exact P_T |]. intros (_ & MMTS_T & _). ss.
    apply DR_concl_fst_silent; [rewrite TR1; apply trace_refine_eq | eapply prtc_step_nstop; eauto |].
    rewrite MMTS_T. exact EX2.
  - destruct C2 as (c_pfx' & rmap' & r' & s' & m' & c_rest & C2). ss. destruct c_pfx'; ss.
  - (* the second-to-last iteration accessed memento m *)
    hexploit simple_prefix_rtc; [exact PFX2 |]. intros (PRE2 & TIME2).
    apply DR_concl_tail with (thr_v := Thread.mk (stmt_continue e0 :: s_r) [LC rmap s_b] ts_r mmts_h).
    + eapply simple_glue with (c_pfx_term := []);
        [exact OK | exact RW_B | exact IH | exact PRE2 | exact TIME2 | ss | exact LAST2
        | exact Z | exact TM | exact EVAL | exact LT |].
      ss. rewrite <- MMTS. exact RTC2.
    + exact SILENT.
    + eapply NSTOP_IF; eauto.
Qed.

(* Lemma H.26, case loop-simple *)
Lemma DR_loop_simple:
  forall env envt labs s_b
    (OK: TypeSystem.env_ok env envt)
    (BODY: EnvType.rw_judge envt labs s_b)
    (IH: DR env s_b),
  DR env [stmt_loop None expr_unit s_b].
Proof.
  intros. apply DR_fold. intros tr tr' thr_term thr_term' [rmap t0] mmts EX1 EX2.
  assert (RW_B: rw_code envt s_b) by (eapply rw_code_judge; eauto).
  destruct (rtc_nil_inv EX1) as [[TR1 THR1] | (tr1 & tr1' & thr1 & TR1 & STEP1 & RTC1)]; subst.
  { apply DR_concl_fst_silent; [apply trace_refine_eq | intro STOP1; unfold STOP in STOP1; des; ss | exact EX2]. }
  destruct (step_loop_inv STEP1) as [TR1a (v1 & EVAL1 & THR1)]. subst. ss.
  destruct (rtc_nil_inv EX2) as [[TR2 THR2] | (tr2 & tr2' & thr2 & TR2 & STEP2 & RTC2)]; subst.
  { apply DR_concl_snd_silent; [exact EX1 | apply trace_refine_eq | reflexivity |].
    intro STOP2; unfold STOP in STOP2; des; ss. }
  destruct (step_loop_inv STEP2) as [TR2a (v2 & EVAL2 & THR2)]. subst. ss.
  hexploit (@loop_cases env [] tr1' _ _ [] rmap None s_b [] RTC1); [reflexivity |].
  intros [ONG | (tr_a & tr_b & s_r & ts_r & mmts_r & TR & BRK & OUT)].
  - (* loop-ongoing *)
    hexploit simple_last_iter; [exact ONG |].
    intros (tr_h & tr_l & t_h & mmts_h & c_pfx & TR & PFX & CONT_TERM & LAST). subst tr1'.
    hexploit simple_prefix_rtc; [exact PFX |]. intros (PRE & TIME_H).
    hexploit touch_cases; [exact OK | exact LAST | split; [ss | econs] |].
    intros [(TR_L & P) | [(SILENT & MMTS & C) | (thr_z & e & m & Z & TM & EVAL & LT)]].
    + (* the last iteration is pure *)
      subst tr_l. hexploit prtc_rtc; [exact OK | exact P |]. intros (_ & MMTS & _). ss.
      destruct PFX as [(T_H & M_H & TR_H) | (e0 & s_r & ts_r & v & PRE_N & EVAL_N & T_H)].
      * subst t_h mmts_h tr_h.
        hexploit prtc_lift; [exact P | apply rw_frame_lc; exact RW_B |]. ss. rewrite <- CONT_TERM.
        destruct thr_term as [st ct tst mt]. ss. intro P1.
        eapply simple_pure_DR; [exact OK | exact P1 | exact EX1 | exact EX2 | exact RTC2].
      * subst t_h.
        eapply simple_second; [exact OK | exact RW_B | exact IH | exact PRE_N | exact EVAL_N | exact RTC1
                               | apply trace_refine_eq | exact MMTS | | exact EX2 | exact RTC2].
        intros t_k mmts_k thr_z e Z TM. rewrite CONT_TERM. intro STOP1. apply STOP_app_loop in STOP1.
        eapply simple_nstop; [exact OK | exact P | exact Z | exact TM | exact STOP1].
    + (* the last iteration is inside a fresh checkpoint *)
      ss. assert (NSTOP: ~ STOP thr_term.(Thread.stmt) thr_term.(Thread.cont)).
      { destruct C as (c_pfx' & rmap' & r' & s' & m' & c_rest & C). rewrite CONT_TERM, C, <- app_assoc.
        intro STOP1. eapply STOP_mid_nonloop; [exact STOP1 | intro L; inv L; ss]. }
      destruct PFX as [(T_H & M_H & TR_H) | (e0 & s_r & ts_r & v & PRE_N & EVAL_N & T_H)].
      * subst t_h mmts_h tr_h.
        apply DR_concl_fst_silent; [exact SILENT | exact NSTOP | rewrite MMTS in EX2; exact EX2].
      * subst t_h.
        eapply simple_second; [exact OK | exact RW_B | exact IH | exact PRE_N | exact EVAL_N | exact RTC1
                               | exact SILENT | exact MMTS | | exact EX2 | exact RTC2].
        i. exact NSTOP.
    + (* the last iteration accessed memento m *)
      eapply simple_glue; [exact OK | exact RW_B | exact IH | exact PRE | exact TIME_H | exact CONT_TERM
                           | exact LAST | exact Z | exact TM | exact EVAL | exact LT | exact RTC2].
  - (* loop-done *)
    hexploit stop_means_no_step; [|exact OUT|]; [left; ss|]. intros [THR TR_B]. subst.
    hexploit simple_last_iter; [exact BRK |].
    intros (tr_h & tr_l & t_h & mmts_h & c_pfx & TR & PFX & CONT_B & LAST). ss.
    assert (c_pfx = []).
    { destruct c_pfx as [|x c_pfx]; ss. inv CONT_B. destruct c_pfx; ss. }
    subst c_pfx tr_a.
    hexploit simple_prefix_rtc; [exact PFX |]. intros (PRE & TIME_H).
    hexploit touch_cases; [exact OK | exact LAST | split; [ss | econs] |].
    intros [(TR_L & P) | [(_ & _ & C) | (thr_z & e & m & Z & TM & EVAL & LT)]].
    + (* the last iteration is pure *)
      subst tr_l. hexploit prtc_rtc; [exact OK | exact P |]. intros (_ & MMTS & _). ss. subst mmts_r.
      destruct PFX as [(T_H & M_H & TR_H) | (e0 & s_r0 & ts_r0 & v & PRE_N & EVAL_N & T_H)].
      * subst t_h mmts_h tr_h.
        hexploit prtc_lift; [exact P | apply rw_frame_lc; exact RW_B |]. ss. intro PL.
        assert (P1: prtc env envt (Thread.mk s_b [LC rmap s_b] (TState.mk rmap t0) mmts)
                         (Thread.mk [] [] (TState.mk rmap (TState.time ts_r)) mmts)).
        { eapply prtc_trans; [exact PL|].
          econs 2; [eapply prtc_rw; [exact OK | exact PL | split; [ss | apply rw_frame_lc; ss]]
                                                   | ss | eapply Thread.step_break; reflexivity | econs 1]. }
        eapply simple_pure_DR; [exact OK | exact P1 | exact EX1 | exact EX2 | exact RTC2].
      * subst t_h. rewrite app_nil_r in RTC1 |- *.
        eapply simple_second; [exact OK | exact RW_B | exact IH | exact PRE_N | exact EVAL_N | exact RTC1
                               | apply trace_refine_eq | ss | | exact EX2 | exact RTC2].
        intros t_k mmts_k thr_z e Z TM. exfalso.
        eapply simple_nstop; [exact OK | exact P | exact Z | exact TM | ss; right; left; eauto].
    + destruct C as (c_pfx' & rmap' & r' & s' & m' & c_rest & C). ss. destruct c_pfx'; ss.
    + rewrite app_nil_r.
      eapply simple_glue_done; [exact OK | exact RW_B | exact IH | exact PRE | exact TIME_H | exact LAST
                                | exact Z | exact TM | exact EVAL | exact LT | exact RTC2].
Qed.
