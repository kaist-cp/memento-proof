Require Import Ensembles EquivDec FunctionalExtensionality List Lia.
Import ListNotations.
Require Import HahnList sflib.
From Memento Require Import Utils Order Syntax Semantics Env Common DR DRRW.
Set Implicit Arguments.

(* Definition H.18 *)
Definition BE (p: Program) : Ensemble (list Event.t) :=
  fun tr => exists mach, Machine.rtc Machine.step p tr (Machine.init p) mach.

Definition B (p: Program) : Ensemble (list Event.t) :=
  fun tr => exists mach, Machine.rtc Machine.normal p tr (Machine.init p) mach.

Definition behaviour (b: list Event.t) : Prop := filter_updates b = b.

Lemma filter_updates_app tr1 tr2:
  filter_updates (tr1 ++ tr2) = filter_updates tr1 ++ filter_updates tr2.
Proof. unfold filter_updates. apply filter_app. Qed.

Lemma filter_updates_idem tr:
  filter_updates (filter_updates tr) = filter_updates tr.
Proof. unfold filter_updates. induction tr as [|ev tr IH]; ss. destruct ev; ss. f_equal. ss. Qed.

Lemma sub_read_filter_updates tr' tr
      (SUB: sub_read tr' tr):
  filter_updates tr' = filter_updates tr.
Proof. unfold filter_updates. induction SUB; ss. destruct ev; ss. f_equal. ss. Qed.

Lemma filter_updates_sub_read tr:
  sub_read (filter_updates tr) tr.
Proof. unfold filter_updates. induction tr as [|ev tr IH]; [econs|]. destruct ev; ss; econs; ss. Qed.

Lemma behaviour_refine b tr
      (BEH: behaviour b):
  b ~ tr <-> b = filter_updates tr.
Proof.
  split.
  - intro REF. apply sub_read_refine in REF. apply sub_read_filter_updates in REF. congr.
  - intro EQ. subst. apply sub_read_refine. apply filter_updates_sub_read.
Qed.

Definition mstep (crash: bool) : Program -> list Event.t -> Machine.t -> Machine.t -> Prop :=
  if crash then Machine.step else Machine.normal.

Lemma mstep_behaviour crash p tr mach mach'
      (RTC: Machine.rtc (mstep crash) p tr mach mach'):
  behaviour tr.
Proof.
  unfold behaviour. induction RTC; ss. subst. rewrite filter_updates_app, IHRTC. f_equal.
  destruct crash; ss; [inv ONE|]; try (inv STEP); try (inv ONE); subst; ss; apply filter_updates_idem.
Qed.

Lemma BE_behaviour p tr
      (BEH: BE p tr):
  behaviour tr.
Proof. destruct BEH as [mach RTC]. eapply (@mstep_behaviour true). exact RTC. Qed.

Inductive rtcX (crash: bool) (env: Env.t) (s_init: list Stmt) : list Event.t -> Thread.t -> Thread.t -> Prop :=
| rtcX_refl
    thr
  : rtcX crash env s_init [] thr thr
| rtcX_step
    tr0 tr1 thr thr0 thr'
    (STEP: Thread.step env tr0 thr thr0)
    (RTC: rtcX crash env s_init tr1 thr0 thr')
  : rtcX crash env s_init (tr0 ++ tr1) thr thr'
| rtcX_crash
    tr thr thr'
    (CRASH: crash = true)
    (RTC: rtcX crash env s_init tr (Thread.mk s_init [] TState.init thr.(Thread.mmts)) thr')
  : rtcX crash env s_init tr thr thr'
.

Lemma rtcX_false env s tr thr thr':
  rtcX false env s tr thr thr' <-> Thread.rtc env [] tr thr thr'.
Proof.
  split; intro RTC.
  - induction RTC; [econs 1 | eapply rtc_nil_step; eauto | congr].
  - induction RTC.
    + econs 1.
    + inv ONE. subst. econs 2; eauto.
Qed.

Lemma rtcX_true env s tr thr thr':
  rtcX true env s tr thr thr' <-> Thread.rtcE env s tr thr thr'.
Proof.
  split; intro RTC.
  - induction RTC.
    + econs 1.
    + econs 2; eauto. econs 1. ss.
    + econs 2; [econs 2 | exact IHRTC | ss].
  - induction RTC; [econs 1|]. subst. inv ONE.
    + econs 2; eauto.
    + econs 3; eauto.
Qed.

Lemma step_trace_shape env tr thr thr'
      (STEP: Thread.step env tr thr thr'):
  tr = [] \/ exists ev, tr = [ev].
Proof. inv STEP; eauto. Qed.

Lemma rtcX_cons_split crash env s ev tr thr thr'
      (RTC: rtcX crash env s (ev :: tr) thr thr'):
  exists thr1 thr2,
    rtcX crash env s [] thr thr1
    /\ Thread.step env [ev] thr1 thr2
    /\ rtcX crash env s tr thr2 thr'.
Proof.
  remember (ev :: tr) as l eqn:L. revert ev tr L.
  induction RTC; i; subst; ss.
  - hexploit step_trace_shape; eauto. i. des; subst; ss.
    + hexploit IHRTC; eauto. i. des. esplits; eauto. rewrite <- (app_nil_l []). econs 2; eauto.
    + inv L. esplits; eauto. econs 1.
  - hexploit IHRTC; eauto. i. des. esplits; eauto. econs 3; eauto.
Qed.

Lemma mem_rtc_app tr1 tr2 mem mem'':
  Mem.rtc (tr1 ++ tr2) mem mem'' <-> exists mem', Mem.rtc tr1 mem mem' /\ Mem.rtc tr2 mem' mem''.
Proof.
  split.
  - revert mem. induction tr1 as [|ev tr1 IH]; ss; i.
    + esplits; eauto. econs 1.
    + inv H. hexploit IH; eauto. i. des. esplits; eauto. econs 2; eauto.
  - intros (mem' & RTC1 & RTC2). induction RTC1; ss. econs 2; eauto.
Qed.

Lemma mem_rtc_sub_read tr mem mem'
      (RTC: Mem.rtc tr mem mem'):
  forall tr', sub_read tr' tr -> Mem.rtc tr' mem mem'.
Proof.
  induction RTC; i.
  - inv H. econs 1.
  - inv H.
    + econs 2; eauto.
    + inv ONE. eauto.
Qed.

Lemma interleaving_sub_read:
  forall (trs: IdMap.t (list Event.t)) tr,
    IdMap.interleaving trs tr ->
  forall trs',
    (forall tid, opt_rel sub_read (IdMap.find tid trs') (IdMap.find tid trs)) ->
  exists tr', IdMap.interleaving trs' tr' /\ sub_read tr' tr.
Proof.
  induction 1; i.
  - exists []. split; [|econs]. econs. ii.
    specialize (H id). rewrite FIND in H. inv H.
    exploit NIL; eauto. i. subst. inv REL. ss.
  - specialize (H0 id) as REL. rewrite FIND in REL. inv REL. rename a0 into tr_id.
    inv REL0.
    + hexploit (IHinterleaving (IdMap.add id a0 trs')).
      { i. rewrite ! IdMap.add_spec. condtac; ss; eauto. }
      i. des. exists (a :: tr'). split.
      * econs; eauto.
      * econs. ss.
    + hexploit (IHinterleaving trs').
      { i. rewrite IdMap.add_spec. destruct (tid == id) as [EQ|NEQ]; ss; eauto.
        inv EQ. rewrite <- H2. eauto. }
      i. des. exists tr'. split; ss. econs. ss.
Qed.

Lemma machine_rtc_trans step p tr1 tr2 m1 m2 m3
      (RTC1: Machine.rtc step p tr1 m1 m2)
      (RTC2: Machine.rtc step p tr2 m2 m3):
  Machine.rtc step p (tr1 ++ tr2) m1 m3.
Proof.
  induction RTC1; subst; ss. econs 2; eauto. rewrite app_assoc. ss.
Qed.

Lemma mstep_normal crash p tr mach mach'
      (STEP: Machine.normal p tr mach mach'):
  mstep crash p tr mach mach'.
Proof. destruct crash; ss. econs 1. ss. Qed.

Lemma machine_silent crash p s tid thr thr'
      (PROG: IdMap.find tid (prog_s p) = Some s)
      (RTC: rtcX crash p.(prog_env) s [] thr thr'):
  forall tmap mem
    (FIND: IdMap.find tid tmap = Some thr),
  Machine.rtc (mstep crash) p [] (Machine.mk tmap mem) (Machine.mk (IdMap.add tid thr' tmap) mem).
Proof.
  remember ([]: list Event.t) as l eqn:L. revert L.
  induction RTC; i; subst.
  - rewrite IdMap.add_find; eauto. econs 1.
  - assert (tr0 = [] /\ tr1 = []) by (apply app_eq_nil; congr). des. subst.
    rewrite <- (IdMap.add_add tid thr' thr0 tmap).
    econs 2; [| eapply IHRTC; eauto | ss].
    + apply mstep_normal. econs; eauto. econs 1.
    + rewrite IdMap.add_spec. condtac; ss. exfalso. apply c. ss.
    + ss.
  - subst. rewrite <- (IdMap.add_add tid thr' (Thread.mk s [] TState.init thr.(Thread.mmts)) tmap).
    econs 2; [| eapply IHRTC; eauto | ss].
    + econs 2. econs; eauto.
    + rewrite IdMap.add_spec. condtac; ss. exfalso. apply c. ss.
    + ss.
Qed.

Lemma machine_embed:
  forall crash p trs tr,
    IdMap.interleaving trs tr ->
  forall tmap mem mem',
    Mem.rtc tr mem mem' ->
    (forall tid tr_t, IdMap.find tid trs = Some tr_t ->
       exists s thr thr', IdMap.find tid (prog_s p) = Some s /\ IdMap.find tid tmap = Some thr
                     /\ rtcX crash p.(prog_env) s tr_t thr thr') ->
  exists tmap', Machine.rtc (mstep crash) p (filter_updates tr) (Machine.mk tmap mem) (Machine.mk tmap' mem').
Proof.
  intros crash p trs tr INTER. induction INTER; i.
  - inv H. exists tmap. econs 1.
  - inv H. hexploit H0; eauto. intros (s & thr & thr' & PROG & FIND_T & RUN).
    hexploit rtcX_cons_split; eauto. intros (thr1 & thr2 & SILENT & STEP & REST).
    hexploit (IHINTER (IdMap.add id thr2 (IdMap.add id thr1 tmap))); eauto.
    { intros tid tr_t FIND'. rewrite IdMap.add_spec in FIND'. destruct (tid == id) as [EQ|NEQ].
      - inv EQ. inv FIND'. exists s, thr2, thr'. rewrite IdMap.add_spec. condtac; ss.
        exfalso. apply c. ss.
      - hexploit H0; eauto. i. des. esplits; eauto.
        rewrite ! IdMap.add_spec. repeat condtac; ss. }
    i. des. exists tmap'.
    change (filter_updates (a :: res)) with ([] ++ filter_updates ([a] ++ res)).
    rewrite filter_updates_app.
    eapply machine_rtc_trans; [eapply machine_silent; eauto|].
    econs 2; [| eauto | ss].
    apply mstep_normal. econs; eauto.
    + ss. rewrite IdMap.add_spec. condtac; ss. exfalso. apply c. ss.
    + econs 2; eauto. econs 1.
Qed.

Lemma machine_project:
  forall crash p tr mach mach',
    Machine.rtc (mstep crash) p tr mach mach' ->
    (forall tid thr, IdMap.find tid mach.(Machine.tmap) = Some thr -> exists s, IdMap.find tid (prog_s p) = Some s) ->
  exists tr_f trs,
    tr = filter_updates tr_f
    /\ IdMap.interleaving trs tr_f
    /\ Mem.rtc tr_f mach.(Machine.mem) mach'.(Machine.mem)
    /\ IdMap.Forall2 (fun tid thr tr_t => exists s thr',
                         IdMap.find tid (prog_s p) = Some s /\ rtcX crash p.(prog_env) s tr_t thr thr')
                     mach.(Machine.tmap) trs.
Proof.
  intros crash p tr mach mach' RTC. induction RTC; intros DOM.
  - exists [], (IdMap.map (fun _ => []) mach.(Machine.tmap)). splits; ss.
    + econs. ii. rewrite IdMap.map_spec in FIND. destruct (IdMap.find id (Machine.tmap mach)); ss. inv FIND. ss.
    + econs 1.
    + intro tid. rewrite IdMap.map_spec. destruct (IdMap.find tid (Machine.tmap mach)) as [thr|] eqn:FIND; ss; econs.
      hexploit DOM; eauto. intros [s PROG]. exists s, thr. split; ss. econs 1.
  - subst.
    assert (STEP: Machine.normal p tr0 mach mach0 \/ (crash = true /\ Machine.crash p tr0 mach mach0)).
    { destruct crash; ss; [inv ONE|]; eauto. }
    clear ONE. destruct STEP as [STEP | (CRASH & STEP)]; inv STEP; ss.
    + (* machine-step *)
      hexploit IHRTC.
      { ss. intros tid' thr' FIND'. rewrite IdMap.add_spec in FIND'. destruct (tid' == tid) as [EQ|NEQ]; eauto.
        inv EQ. eapply DOM; eauto. }
      intros (tr_f & trs & TR & INTER & MEM & LOCAL). subst.
      specialize (LOCAL tid) as LT. ss. rewrite IdMap.add_spec in LT.
      destruct (tid == tid) as [_|NEQ]; [|exfalso; apply NEQ; ss].
      inv LT. rename b into l. destruct REL as (s & thr' & PROG & RUN).
      exists (tr_t ++ tr_f), (IdMap.add tid (tr_t ++ l) trs). splits.
      * rewrite filter_updates_app. ss.
      * hexploit step_trace_shape; eauto. intros [TR_T | (ev & TR_T)]; subst; ss.
        -- rewrite IdMap.add_find; ss.
        -- eapply IdMap.interleaving_cons with (id := tid).
           ++ rewrite IdMap.add_spec. destruct (tid == tid) as [_|NEQ]; [reflexivity | exfalso; apply NEQ; ss].
           ++ rewrite IdMap.add_add. rewrite IdMap.add_find; ss.
      * apply mem_rtc_app. esplits; eauto.
      * intro tid'. rewrite IdMap.add_spec. condtac.
        -- clear X. inv e. rewrite THR1. econs. exists s, thr'. split; ss. econs 2; eauto.
        -- specialize (LOCAL tid'). ss. rewrite IdMap.add_spec, X in LOCAL. ss.
    + (* machine-crash *)
      hexploit IHRTC.
      { ss. intros tid' thr' FIND'. rewrite IdMap.add_spec in FIND'. destruct (tid' == tid) as [EQ|NEQ]; eauto.
        inv EQ. eapply DOM; eauto. }
      intros (tr_f & trs & TR & INTER & MEM & LOCAL). subst.
      exists tr_f, trs. splits; ss.
      intro tid'. specialize (LOCAL tid'). ss. rewrite IdMap.add_spec in LOCAL. revert LOCAL. condtac; intro LOCAL.
      * clear X. inv e. rewrite THR1. inv LOCAL. econs. destruct REL as (s' & thr' & PROG & RUN).
        rewrite STMT in PROG. inv PROG. exists s', thr'. split; ss. econs 3; eauto.
      * ss.
Qed.

Lemma init_dom p tid thr
      (FIND: IdMap.find tid (Machine.init p).(Machine.tmap) = Some thr):
  exists s, IdMap.find tid (prog_s p) = Some s /\ thr = Machine.init_thread s.
Proof.
  rewrite Machine.init_find in FIND. destruct (IdMap.find tid (prog_s p)) eqn:PROG; ss. inv FIND. eauto.
Qed.

Lemma project_init crash p tr mach
      (RTC: Machine.rtc (mstep crash) p tr (Machine.init p) mach):
  exists tr_f trs,
    tr = filter_updates tr_f
    /\ IdMap.interleaving trs tr_f
    /\ Mem.rtc tr_f Mem.init mach.(Machine.mem)
    /\ IdMap.Forall2 (fun _ s tr_t => exists thr, rtcX crash p.(prog_env) s tr_t (Machine.init_thread s) thr)
                     (prog_s p) trs.
Proof.
  hexploit machine_project; eauto.
  { intros tid thr FIND. apply init_dom in FIND. des. eauto. }
  intros (tr_f & trs & TR & INTER & MEM & LOCAL).
  exists tr_f, trs. splits; ss.
  intro tid. specialize (LOCAL tid). ss. rewrite IdMap.map_spec in LOCAL.
  destruct (IdMap.find tid (prog_s p)) as [s|] eqn:PROG; ss; inv LOCAL; econs.
  destruct REL as (s' & thr' & PROG' & RUN). inv PROG'. eauto.
Qed.

Lemma embed_init crash p trs tr mem
      (INTER: IdMap.interleaving trs tr)
      (MEM: Mem.rtc tr Mem.init mem)
      (RUNS: IdMap.Forall2 (fun _ s tr_t => exists thr, rtcX crash p.(prog_env) s tr_t (Machine.init_thread s) thr)
                           (prog_s p) trs):
  exists mach,
    Machine.rtc (mstep crash) p (filter_updates tr) (Machine.init p) mach
    /\ mach.(Machine.mem) = mem.
Proof.
  hexploit (@machine_embed crash p trs tr INTER (Machine.init p).(Machine.tmap) Mem.init mem); eauto.
  { intros tid tr_t FIND. specialize (RUNS tid). rewrite FIND in RUNS. inv RUNS. destruct REL as (thr & RUN).
    match goal with [H: Some _ = IdMap.find _ (prog_s _) |- _] => rename H into PROG end.
    exists a, (Machine.init_thread a), thr. splits; ss. rewrite IdMap.map_spec, <- PROG. ss. }
  intros (tmap' & RTC). eexists. split; [exact RTC | ss].
Qed.

Lemma runs_mon (R1 R2: list Stmt -> list Event.t -> Thread.t -> Prop) p trs
      (MON: forall s tr_t thr, R1 s tr_t thr -> R2 s tr_t thr)
      (RUNS: IdMap.Forall2 (fun _ s tr_t => exists thr, R1 s tr_t thr) (prog_s p) trs):
  IdMap.Forall2 (fun _ s tr_t => exists thr, R2 s tr_t thr) (prog_s p) trs.
Proof. intro tid. specialize (RUNS tid). inv RUNS; econs. destruct REL as (thr & RUN). eauto. Qed.

Lemma runs_thrs (R: list Stmt -> list Event.t -> Thread.t -> Prop) p trs:
  IdMap.Forall2 (fun _ s tr_t => exists thr, R s tr_t thr) (prog_s p) trs
  <-> exists thrs,
      forall tid,
        match IdMap.find tid (prog_s p), IdMap.find tid trs, IdMap.find tid thrs with
        | Some s, Some tr_t, Some thr => R s tr_t thr
        | None, None, None => True
        | _, _, _ => False
        end.
Proof.
  split.
  - intro RUNS.
    hexploit (IdMap.finite_choice
                (fun tid tr_t thr => exists s, IdMap.find tid (prog_s p) = Some s /\ R s tr_t thr) trs).
    { intros tid tr_t FIND. specialize (RUNS tid). rewrite FIND in RUNS. inv RUNS. destruct REL as (thr & RUN).
      eauto. }
    intros [thrs REL]. exists thrs. intro tid. specialize (RUNS tid). specialize (REL tid).
    destruct (IdMap.find tid (prog_s p)) as [s|] eqn:PROG, (IdMap.find tid trs) as [tr_t|] eqn:TRS,
             (IdMap.find tid thrs) as [thr|] eqn:THRS; inv RUNS; inv REL; ss.
    des. match goal with [H: Some _ = Some _ |- _] => inv H end. ss.
  - intros (thrs & RUNS) tid. specialize (RUNS tid).
    destruct (IdMap.find tid (prog_s p)), (IdMap.find tid trs), (IdMap.find tid thrs); ss; econs; eauto.
Qed.

(* Lemma H.20 *)
Lemma crash_free_interleaving:
  forall p b,
    behaviour b ->
    (B p b <->
     exists tr mem trs thrs,
       Mem.rtc tr Mem.init mem
       /\ IdMap.interleaving trs tr
       /\ (forall tid,
             match IdMap.find tid (prog_s p), IdMap.find tid trs, IdMap.find tid thrs with
             | Some s, Some tr_t, Some thr => Thread.rtc p.(prog_env) [] tr_t (Machine.init_thread s) thr
             | None, None, None => True
             | _, _, _ => False
             end)
       /\ b ~ tr).
Proof.
  intros p b BEH. split.
  - intros (mach & RTC). hexploit (@project_init false); eauto. intros (tr_f & trs & TR & INTER & MEM & RUNS).
    hexploit (@runs_mon
                (fun s tr_t thr => rtcX false p.(prog_env) s tr_t (Machine.init_thread s) thr)
                (fun s tr_t thr => Thread.rtc p.(prog_env) [] tr_t (Machine.init_thread s) thr) p trs);
      [intros s0 tr0 thr0 RUN0; exact (proj1 (rtcX_false _ _ _ _ _) RUN0) | exact RUNS |].
    intro RUNS1. apply runs_thrs in RUNS1. destruct RUNS1 as (thrs & RUNS1).
    exists tr_f, mach.(Machine.mem), trs, thrs. splits; ss. apply behaviour_refine; ss.
  - intros (tr & mem & trs & thrs & MEM & INTER & RUNS & REF).
    apply behaviour_refine in REF; ss. subst.
    hexploit (proj2 (runs_thrs (fun s tr_t thr => Thread.rtc p.(prog_env) [] tr_t (Machine.init_thread s) thr)
                               p trs)); [eauto|].
    intro RUNS1.
    hexploit (@runs_mon
                (fun s tr_t thr => Thread.rtc p.(prog_env) [] tr_t (Machine.init_thread s) thr)
                (fun s tr_t thr => rtcX false p.(prog_env) s tr_t (Machine.init_thread s) thr) p trs);
      [intros s0 tr0 thr0 RUN0; exact (proj2 (rtcX_false _ _ _ _ _) RUN0) | exact RUNS1 |].
    intro RUNS2. hexploit (@embed_init false); eauto. intros (mach & RTC & _). eexists. eauto.
Qed.

(* Lemma H.21 *)
Lemma interleaving:
  forall p b,
    behaviour b ->
    (BE p b <->
     exists tr mem trs thrs,
       Mem.rtc tr Mem.init mem
       /\ IdMap.interleaving trs tr
       /\ (forall tid,
             match IdMap.find tid (prog_s p), IdMap.find tid trs, IdMap.find tid thrs with
             | Some s, Some tr_t, Some thr => Thread.rtcE p.(prog_env) s tr_t (Machine.init_thread s) thr
             | None, None, None => True
             | _, _, _ => False
             end)
       /\ b ~ tr).
Proof.
  intros p b BEH. split.
  - intros (mach & RTC). hexploit (@project_init true); eauto. intros (tr_f & trs & TR & INTER & MEM & RUNS).
    hexploit (@runs_mon
                (fun s tr_t thr => rtcX true p.(prog_env) s tr_t (Machine.init_thread s) thr)
                (fun s tr_t thr => Thread.rtcE p.(prog_env) s tr_t (Machine.init_thread s) thr) p trs);
      [intros s0 tr0 thr0 RUN0; exact (proj1 (rtcX_true _ _ _ _ _) RUN0) | exact RUNS |].
    intro RUNS1. apply runs_thrs in RUNS1. destruct RUNS1 as (thrs & RUNS1).
    exists tr_f, mach.(Machine.mem), trs, thrs. splits; ss. apply behaviour_refine; ss.
  - intros (tr & mem & trs & thrs & MEM & INTER & RUNS & REF).
    apply behaviour_refine in REF; ss. subst.
    hexploit (proj2 (runs_thrs (fun s tr_t thr => Thread.rtcE p.(prog_env) s tr_t (Machine.init_thread s) thr)
                               p trs)); [eauto|].
    intro RUNS1.
    hexploit (@runs_mon
                (fun s tr_t thr => Thread.rtcE p.(prog_env) s tr_t (Machine.init_thread s) thr)
                (fun s tr_t thr => rtcX true p.(prog_env) s tr_t (Machine.init_thread s) thr) p trs);
      [intros s0 tr0 thr0 RUN0; exact (proj2 (rtcX_true _ _ _ _ _) RUN0) | exact RUNS1 |].
    intro RUNS2. hexploit (@embed_init true); eauto. intros (mach & RTC & _). eexists. eauto.
Qed.

Lemma remove_crashes:
  forall env s tr thr thr',
    DR env s ->
    Thread.rtcE env s tr thr thr' ->
  forall tr0 mmts,
    Thread.rtc env [] tr0 (Thread.mk s [] TState.init mmts) thr ->
  exists tr_x thr_x,
    Thread.rtc env [] tr_x (Thread.mk s [] TState.init mmts) thr_x
    /\ tr_x ~ tr0 ++ tr
    /\ thr_x.(Thread.mmts) = thr'.(Thread.mmts).
Proof.
  intros env s tr thr thr' DR_S RUN. induction RUN; intros tr_p mmts PRE.
  { esplits; [exact PRE | rewrite app_nil_r; apply trace_refine_eq | ss]. }
  subst. inv ONE.
  - hexploit (IHRUN (tr_p ++ tr0) mmts); [eapply rtc_app; [exact PRE | eapply rtc_one; eauto | ss] |].
    intros (tr_x & thr_x & RTC & REF & MMTS). rewrite <- app_assoc in REF. eauto.
  - hexploit (IHRUN [] thr.(Thread.mmts)); [econs 1 |]. intros (tr_y & thr_y & RTC_Y & REF_Y & MMTS_Y).
    destruct (DR_elim DR_S PRE RTC_Y) as (tr_x & s_x & c_x & ts_x & TRACE & REFINE & _ & _).
    exists tr_x, (Thread.mk s_x c_x ts_x thr_y.(Thread.mmts)). splits; ss.
    eapply trace_refine_trans; [exact REFINE|]. apply trace_refine_app; [exact REF_Y | apply trace_refine_eq].
Qed.

Lemma prog_s_in A:
  forall (ss: list A) tid k s,
    IdMap.find k (tmap_of tid ss) = Some s ->
  List.In s ss.
Proof.
  induction ss as [|s0 ss IH]; ss; i.
  - rewrite IdMap.gempty in H. ss.
  - rewrite IdMap.add_spec in H. destruct (k == tid); [inv H; left; ss | right; eauto].
Qed.

Lemma remove_crashes_all:
  forall p envt trs,
    TypeSystem.judge p.(prog_env) envt ->
    Forall (fun s => exists labs, EnvType.rw_judge envt labs s) p.(prog_threads) ->
    IdMap.Forall2 (fun _ s tr_t => exists thr, Thread.rtcE p.(prog_env) s tr_t (Machine.init_thread s) thr)
                  (prog_s p) trs ->
  exists trs',
    (forall tid, opt_rel sub_read (IdMap.find tid trs') (IdMap.find tid trs))
    /\ IdMap.Forall2 (fun _ s tr_t => exists thr, Thread.rtc p.(prog_env) [] tr_t (Machine.init_thread s) thr)
                     (prog_s p) trs'.
Proof.
  intros p envt trs JUDGE TYPED RUNS.
  hexploit (IdMap.finite_choice
              (fun tid tr_t tr_t' =>
                 sub_read tr_t' tr_t
                 /\ exists s thr, IdMap.find tid (prog_s p) = Some s
                            /\ Thread.rtc p.(prog_env) [] tr_t' (Machine.init_thread s) thr)
              trs).
  { intros tid tr_t FIND. specialize (RUNS tid). rewrite FIND in RUNS. inv RUNS. destruct REL as (thr & RUN).
    match goal with [H: Some _ = IdMap.find _ (prog_s _) |- _] => rename H into PROG end.
    assert (TY: exists labs, EnvType.rw_judge envt labs a).
    { rewrite Forall_forall in TYPED. apply TYPED. eapply prog_s_in. symmetry. exact PROG. }
    destruct TY as (labs & TY).
    hexploit remove_crashes; [eapply DR_RW; eauto | exact RUN | econs 1 |].
    intros (tr_x & thr_x & RTC & REF_X & _). ss.
    exists tr_x. split; [apply sub_read_refine; ss|]. esplits; eauto. }
  intros [trs' REL]. exists trs'. split.
  - intro tid. specialize (REL tid). inv REL; econs. des. ss.
  - intro tid. specialize (RUNS tid). specialize (REL tid).
    destruct (IdMap.find tid (prog_s p)) as [s|] eqn:PROG, (IdMap.find tid trs) as [tr_t|] eqn:TRS,
             (IdMap.find tid trs') as [tr_t'|] eqn:TRS'; inv RUNS; inv REL; econs.
    des. match goal with [H: Some _ = Some _ |- _] => inv H end. eauto.
Qed.

(* Theorem 3.1 (H.24) *)
Theorem detectability:
  forall p,
    TypeSystem.prog_judge p ->
  Included _ (BE p) (B p).
Proof.
  intros p (envt & JUDGE & TYPED) b BE_B.
  assert (BEH: behaviour b) by (eapply BE_behaviour; eauto).
  apply (interleaving p BEH) in BE_B. destruct BE_B as (tr & mem & trs & thrs & MEM & INTER & RUNS & REF).
  apply (crash_free_interleaving p BEH).
  hexploit (@remove_crashes_all p envt trs); eauto.
  { apply runs_thrs. eauto. }
  intros (trs' & SUB & RUNS1).
  hexploit (@interleaving_sub_read trs tr INTER trs' SUB). intros (tr' & INTER' & SUB').
  apply runs_thrs in RUNS1. destruct RUNS1 as (thrs' & RUNS1).
  exists tr', mem, trs', thrs'. splits; ss.
  - eapply mem_rtc_sub_read; eauto.
  - apply behaviour_refine; ss. apply behaviour_refine in REF; ss. rewrite REF.
    symmetry. apply sub_read_filter_updates. ss.
Qed.

Lemma machine_remove_crashes:
  forall p,
    TypeSystem.prog_judge p ->
  forall tr mach,
    Machine.rtc Machine.step p tr (Machine.init p) mach ->
  exists mach',
    Machine.rtc Machine.normal p tr (Machine.init p) mach'
    /\ mach'.(Machine.mem) = mach.(Machine.mem).
Proof.
  intros p (envt & JUDGE & TYPED) tr mach RUN.
  hexploit (@project_init true); eauto. intros (tr_f & trs & TR & INTER & MEM & RUNS). subst tr.
  hexploit (@runs_mon
              (fun s tr_t thr => rtcX true p.(prog_env) s tr_t (Machine.init_thread s) thr)
              (fun s tr_t thr => Thread.rtcE p.(prog_env) s tr_t (Machine.init_thread s) thr) p trs);
    [intros s0 tr0 thr0 RUN0; exact (proj1 (rtcX_true _ _ _ _ _) RUN0) | exact RUNS |].
  intro RUNS1. hexploit (@remove_crashes_all p envt trs); eauto. intros (trs' & SUB & RUNS2).
  hexploit (@interleaving_sub_read trs tr_f INTER trs' SUB). intros (tr_f' & INTER' & SUB').
  hexploit (@runs_mon
              (fun s tr_t thr => Thread.rtc p.(prog_env) [] tr_t (Machine.init_thread s) thr)
              (fun s tr_t thr => rtcX false p.(prog_env) s tr_t (Machine.init_thread s) thr) p trs');
    [intros s0 tr0 thr0 RUN0; exact (proj2 (rtcX_false _ _ _ _ _) RUN0) | exact RUNS2 |].
  intro RUNS3. hexploit (@embed_init false p trs' tr_f' mach.(Machine.mem)); eauto.
  { eapply mem_rtc_sub_read; eauto. }
  intros (mach' & RTC & MEM'). exists mach'. split; ss.
  erewrite <- sub_read_filter_updates; eauto.
Qed.
