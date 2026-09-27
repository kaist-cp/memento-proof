Require Import EquivDec.
Require Import Ensembles.
Require Import Arith.
Require Import Lia.
Require Import List.
Import ListNotations.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Order.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Env.
From Memento Require Import Common.
From Memento Require Import Lifting.
From Memento Require Import Detectability.
From Memento Require Import Erased.

Set Implicit Arguments.

Definition last_mid (prms: list VReg) : bool :=
  match rev prms with
  | x :: _ => Nat.eqb x mid
  | [] => false
  end.

Definition rw_fn (env: Env.t) (f: FnId) : bool :=
  match IdMap.find f env with
  | Some (prms, _) => last_mid prms
  | None => false
  end.

Fixpoint erase_stmt (env: Env.t) (x: Stmt) : EStmt :=
  match x with
  | stmt_assign r e => estmt_assign r e
  | stmt_pload r e => estmt_pload r e
  | stmt_palloc r e => estmt_palloc r e
  | stmt_if e s_t s_f => estmt_if e (map (erase_stmt env) s_t) (map (erase_stmt env) s_f)
  | stmt_loop r e s => estmt_loop r e (map (erase_stmt env) s)
  | stmt_continue e => estmt_continue e
  | stmt_break => estmt_break
  | stmt_call r f es => estmt_call r f (if rw_fn env f then removelast es else es)
  | stmt_return e => estmt_return e
  | stmt_chkpt r s _ => estmt_blk r (map (erase_stmt env) s)
  | stmt_pcas r e_loc e_old e_new _ => estmt_cas r e_loc e_old e_new
  end.

Definition erase_stmts (env: Env.t) (s: list Stmt) : list EStmt := map (erase_stmt env) s.

Definition erase_env (env: Env.t) : EEnv.t :=
  IdMap.map (fun fn => (if last_mid (fst fn) then removelast (fst fn) else fst fn, erase_stmts env (snd fn))) env.

Definition erase (p: Program) : EProgram :=
  mk_eprogram (erase_env p.(prog_env)) (map (erase_stmts p.(prog_env)) p.(prog_threads)).

Lemma last_mid_app prms:
  last_mid (prms ++ [mid]) = true.
Proof. unfold last_mid. rewrite rev_app_distr. ss. Qed.

Lemma last_mid_nin prms
      (NIN: ~ List.In mid prms):
  last_mid prms = false.
Proof.
  unfold last_mid. destruct (rev prms) as [|x l] eqn:REV; ss.
  destruct (Nat.eqb x mid) eqn:EQ; ss. apply Nat.eqb_eq in EQ. subst.
  exfalso. apply NIN. apply in_rev. rewrite REV. left. ss.
Qed.

Lemma erase_find_rw env f prms s_f
      (FIND: IdMap.find f env = Some (prms ++ [mid], s_f)):
  rw_fn env f = true /\ IdMap.find f (erase_env env) = Some (prms, erase_stmts env s_f).
Proof.
  unfold rw_fn, erase_env. rewrite FIND, IdMap.map_spec, FIND. ss. rewrite last_mid_app, removelast_last. ss.
Qed.

Lemma erase_find_ro env f prms s_f
      (FIND: IdMap.find f env = Some (prms, s_f))
      (NIN: ~ List.In mid prms):
  rw_fn env f = false /\ IdMap.find f (erase_env env) = Some (prms, erase_stmts env s_f).
Proof.
  unfold rw_fn, erase_env. rewrite FIND, IdMap.map_spec, FIND. ss. rewrite last_mid_nin; ss.
Qed.

Definition regs_rel (md: bool) (rmap rmap': VRegMap.t) : Prop :=
  if md then forall r, r <> mid -> rmap r = rmap' r else rmap = rmap'.

Lemma regs_rel_add md r v rmap rmap'
      (REL: regs_rel md rmap rmap'):
  regs_rel md (VRegMap.add r v rmap) (VRegMap.add r v rmap').
Proof.
  destruct md; ss; [|subst; ss]. intros r' NEQ.
  destruct (r' == r) as [EQ|NEQ']; [inv EQ; rewrite ! VRegMap.add_eq; ss|].
  rewrite ! VRegMap.add_neq; eauto.
Qed.

Lemma regs_rel_set_opt md r v rmap rmap'
      (REL: regs_rel md rmap rmap'):
  regs_rel md (set_opt r v rmap) (set_opt r v rmap').
Proof. destruct r; ss. apply regs_rel_add. ss. Qed.

Lemma sem_expr_free:
  forall e rmap rmap',
    (forall r, free_in r e -> rmap r = rmap' r) ->
  sem_expr rmap e = sem_expr rmap' e.
Proof.
  induction e; i; ss.
  - apply H. ss.
  - rewrite (IHe1 rmap rmap'), (IHe2 rmap rmap'); eauto.
  - rewrite (IHe rmap rmap'); eauto.
  - rewrite (IHe1 rmap rmap'), (IHe2 rmap rmap'); eauto.
  - rewrite (IHe rmap rmap'); eauto.
  - rewrite (IHe rmap rmap'); eauto.
  - rewrite (IHe1 rmap rmap'); eauto. destruct (sem_expr rmap' e1) as [[]|]; ss.
    + apply IHe2. intros r0 FREE. destruct (r0 == xl) as [EQ|NEQ]; [inv EQ; rewrite ! VRegMap.add_eq; ss|].
      rewrite ! VRegMap.add_neq; eauto.
    + apply IHe3. intros r0 FREE. destruct (r0 == xr) as [EQ|NEQ]; [inv EQ; rewrite ! VRegMap.add_eq; ss|].
      rewrite ! VRegMap.add_neq; eauto.
  - rewrite (IHe rmap rmap'); eauto.
Qed.

Lemma eval_rel md rmap rmap' e
      (REL: regs_rel md rmap rmap')
      (MF: md = true -> midfree e):
  sem_expr rmap e = sem_expr rmap' e.
Proof.
  destruct md; ss; [|subst; ss]. apply sem_expr_free. intros r FREE. apply REL.
  intro EQ. subst. apply MF; ss.
Qed.

Lemma evals_rel md rmap rmap' es
      (REL: regs_rel md rmap rmap')
      (MF: md = true -> Forall midfree es):
  sem_exprs rmap es = sem_exprs rmap' es.
Proof.
  induction es as [|e es IH]; ss.
  rewrite (@eval_rel md rmap rmap' e), IH; ss.
  - i. hexploit MF; ss. intro FA. inv FA. ss.
  - i. hexploit MF; ss. intro FA. inv FA. ss.
Qed.

Lemma bind_params_mid prms vs v
      (LEN: length prms = length vs):
  regs_rel true (bind_params (prms ++ [mid]) (vs ++ [v])) (bind_params prms vs).
Proof.
  revert vs LEN. induction prms as [|p prms IH]; destruct vs as [|v0 vs]; intros LEN; try (simpl in LEN; lia).
  - intros r NEQ. simpl. rewrite VRegMap.add_neq; ss.
  - exact (@regs_rel_add true p v0 _ _ (IH vs ltac:(simpl in LEN; lia))).
Qed.

Definition tcode (envt: EnvType.t) (s: list Stmt) : Prop :=
  Forall (fun x => (exists labs, EnvType.rw_judge envt labs [x])
                   \/ (EnvType.ro_judge envt [x] /\ midfree_stmt x)) s.

Definition rcode (envt: EnvType.t) (s: list Stmt) : Prop :=
  Forall (fun x => EnvType.ro_judge envt [x]) s.

Definition code (envt: EnvType.t) (md: bool) (s: list Stmt) : Prop :=
  if md then tcode envt s else rcode envt s.

Lemma tcode_rw envt labs s
      (RW: EnvType.rw_judge envt labs s):
  tcode envt s.
Proof.
  eapply Forall_impl; [|apply EnvShape.rw_judge_forall; exact RW]. intros x (labs' & _ & RW'). left. eauto.
Qed.

Lemma tcode_ro envt s
      (RO: EnvType.ro_judge envt s)
      (MF: midfree_stmts s):
  tcode envt s.
Proof.
  apply EnvShape.ro_judge_forall in RO. induction RO as [|x s X RO IH]; econs.
  - right. split; ss. apply MF.
  - apply IH. apply MF.
Qed.

Lemma rcode_ro envt s
      (RO: EnvType.ro_judge envt s):
  rcode envt s.
Proof. apply EnvShape.ro_judge_forall. ss. Qed.

Lemma code_app envt md s1 s2
      (CODE1: code envt md s1)
      (CODE2: code envt md s2):
  code envt md (s1 ++ s2).
Proof. destruct md; ss; apply Forall_app; ss. Qed.

Lemma code_head:
  forall env envt md x s,
    TypeSystem.env_ok env envt ->
    code envt md (x :: s) ->
  code envt md s
  /\ match x with
     | stmt_assign _ e | stmt_pload _ e | stmt_palloc _ e
     | stmt_continue e | stmt_return e => md = true -> midfree e
     | stmt_if e s_t s_f => (md = true -> midfree e) /\ code envt md s_t /\ code envt md s_f
     | stmt_loop _ e s_b => (md = true -> midfree e) /\ code envt md s_b
     | stmt_break => True
     | stmt_call _ f es =>
         (md = true /\ exists es' lab prms s_f,
             es = es' ++ [expr_mid lab] /\ Forall midfree es'
             /\ IdMap.find f env = Some (prms ++ [mid], s_f) /\ tcode envt s_f)
         \/ (exists prms s_f,
               (md = true -> Forall midfree es)
               /\ IdMap.find f env = Some (prms, s_f) /\ rcode envt s_f /\ ~ List.In mid prms)
     | stmt_chkpt _ s_c _ => md = true /\ tcode envt s_c
     | stmt_pcas _ e_loc e_old e_new _ => md = true /\ midfree e_loc /\ midfree e_old /\ midfree e_new
     end.
Proof.
  intros env envt md x s [OK_RO OK_RW] CODE.
  assert (HEAD: if md
                then (exists labs, EnvType.rw_judge envt labs [x]) \/ (EnvType.ro_judge envt [x] /\ midfree_stmt x)
                else EnvType.ro_judge envt [x]).
  { destruct md; ss; inv CODE; ss. }
  split; [destruct md; ss; inv CODE; ss|].
  destruct md.
  - destruct HEAD as [(labs & RW) | (RO & MF)].
    + apply EnvShape.rw_judge_single in RW.
      destruct x as [r e|r e|r e|e s_t s_f|[r|] e s_b|e| |r f es|e|r s_c e_mid|r el eo en em]; ss; des; subst.
      * i. ss.
      * splits; [i; ss | eapply tcode_rw; eauto | eapply tcode_rw; eauto].
      * split; [i; ss|]. econs; [left; eexists; apply loop_head_rw; ss | eapply tcode_rw; eauto].
      * split; [intros _ FREE; ss | eapply tcode_rw; eauto].
      * left. split; ss. hexploit OK_RW; eauto. intros (prms & labs' & s_f & FIND & RW_F & _).
        esplits; eauto. eapply tcode_rw; eauto.
      * split; ss. apply tcode_ro; ss.
      * splits; ss.
    + apply EnvShape.ro_judge_single in RO.
      destruct x as [r e|r e|r e|e s_t s_f|r e s_b|e| |r f es|e|r s_c e_mid|r el eo en em]; ss; des.
      * splits; [i; ss | apply tcode_ro; ss | apply tcode_ro; ss].
      * split; [i; ss | apply tcode_ro; ss].
      * right. hexploit OK_RO; eauto. intros (prms & s_f & FIND & RO_F & NODUP & NIN).
        esplits; eauto. apply rcode_ro. ss.
  - apply EnvShape.ro_judge_single in HEAD.
    destruct x as [r e|r e|r e|e s_t s_f|r e s_b|e| |r f es|e|r s_c e_mid|r el eo en em]; ss; des.
    + splits; [i; ss | apply rcode_ro; ss | apply rcode_ro; ss].
    + split; [i; ss | apply rcode_ro; ss].
    + right. hexploit OK_RO; eauto. intros (prms & s_f & FIND & RO_F & NODUP & NIN).
      esplits; eauto; [i; ss | apply rcode_ro; ss].
Qed.

Inductive stack_rel (env: Env.t) (envt: EnvType.t) : bool -> list Cont.t -> list ECont.t -> Prop :=
| stack_nil
  : stack_rel env envt true [] []
| stack_loop
    md rmap rmap' r s_b s_c c ec
    (REGS: regs_rel md rmap rmap')
    (CODE_B: code envt md s_b)
    (CODE_C: code envt md s_c)
    (REST: stack_rel env envt md c ec)
  : stack_rel env envt md (Cont.loopcont rmap r s_b s_c :: c)
              (ECont.loopcont rmap' r (erase_stmts env s_b) (erase_stmts env s_c) :: ec)
| stack_fn
    md md' rmap rmap' r s_c c ec
    (REGS: regs_rel md' rmap rmap')
    (CODE: code envt md' s_c)
    (REST: stack_rel env envt md' c ec)
  : stack_rel env envt md (Cont.fncont rmap r s_c :: c) (ECont.fncont rmap' r (erase_stmts env s_c) :: ec)
| stack_chkpt
    rmap rmap' r s_c m c ec
    (REGS: regs_rel true rmap rmap')
    (CODE: code envt true s_c)
    (REST: stack_rel env envt true c ec)
  : stack_rel env envt true (Cont.chkptcont rmap r s_c m :: c) (ECont.blkcont rmap' r (erase_stmts env s_c) :: ec)
.

Definition tsim (env: Env.t) (envt: EnvType.t) (thr: Thread.t) (ethr: EThread.t) : Prop :=
  exists md,
    regs_rel md thr.(Thread.ts).(TState.regs) ethr.(EThread.regs)
    /\ code envt md thr.(Thread.stmt)
    /\ ethr.(EThread.stmt) = erase_stmts env thr.(Thread.stmt)
    /\ stack_rel env envt md thr.(Thread.cont) ethr.(EThread.cont)
    /\ forall m, (thr.(Thread.mmts) m).(Mmt.time) <= thr.(Thread.ts).(TState.time).

Lemma stack_rel_pop:
  forall env envt c_loops md x c2 ec,
    stack_rel env envt md (c_loops ++ x :: c2) ec ->
    Cont.Loops c_loops ->
  exists ec_loops ec2,
    ECont.Loops ec_loops
    /\ match x with
       | Cont.fncont rmap r s_c =>
           exists md' rmap', ec = ec_loops ++ ECont.fncont rmap' r (erase_stmts env s_c) :: ec2
                        /\ regs_rel md' rmap rmap' /\ code envt md' s_c /\ stack_rel env envt md' c2 ec2
       | Cont.chkptcont rmap r s_c _ =>
           exists rmap', ec = ec_loops ++ ECont.blkcont rmap' r (erase_stmts env s_c) :: ec2
                    /\ md = true /\ regs_rel true rmap rmap' /\ code envt true s_c /\ stack_rel env envt true c2 ec2
       | Cont.loopcont _ _ _ _ => True
       end.
Proof.
  induction c_loops as [|y c_loops IH]; intros md x c2 ec STACK LOOPS; ss.
  - inv STACK; exists [], ec0; (split; [econs|]); ss; esplits; eauto.
  - inversion LOOPS as [|? ? IS LOOPS']. subst. destruct y; ss; try by inv IS.
    inv STACK. hexploit IH; eauto. intros (ec_loops & ec2 & ELOOPS & X).
    exists (ECont.loopcont rmap' r (erase_stmts env s_body) (erase_stmts env s_cont) :: ec_loops), ec2. split.
    + econs; ss.
    + destruct x; ss; des; subst; esplits; eauto.
Qed.

Lemma sim_step:
  forall env envt tr thr thr' ethr,
    TypeSystem.env_ok env envt ->
    Thread.step env tr thr thr' ->
    tsim env envt thr ethr ->
  exists ethr', EThread.step (erase_env env) tr ethr ethr' /\ tsim env envt thr' ethr'.
Proof.
  intros env envt tr thr thr' ethr OK STEP (md & REGS & CODE & STMT & STACK & NR).
  destruct ethr as [es ec regs']. ss. subst es.
  inv STEP; ss; hexploit code_head; eauto; intros [CODE' HEAD]; ss.
  - (* assign *)
    esplits; [econs; rewrite <- (@eval_rel _ _ _ _ REGS HEAD); exact EVAL|].
    exists md. splits; ss. apply regs_rel_add. ss.
  - (* pload *)
    esplits; [econs; [rewrite <- (@eval_rel _ _ _ _ REGS HEAD); exact EVAL | exact LOC]|].
    exists md. splits; ss. apply regs_rel_add. ss.
  - (* palloc *)
    esplits; [econs; rewrite <- (@eval_rel _ _ _ _ REGS HEAD); exact EVAL|].
    exists md. splits; ss. apply regs_rel_add. ss.
  - (* branch *)
    destruct HEAD as (MF & CODE_T & CODE_F).
    esplits; [econs; rewrite <- (@eval_rel _ _ _ _ REGS MF); exact EVAL|].
    exists md. splits; ss.
    + apply code_app; ss. destruct b; ss.
    + unfold erase_stmts. rewrite map_app. destruct b; ss.
  - (* loop *)
    destruct HEAD as (MF & CODE_B).
    esplits; [econs; rewrite <- (@eval_rel _ _ _ _ REGS MF); exact EVAL|].
    exists md. splits; ss.
    + apply regs_rel_set_opt. ss.
    + econs; ss.
  - (* continue *)
    inversion STACK as [| ? rmap0 rmap' r0 s_b s_c c0 ec0 REGS0 CODE_B CODE_C REST | |]; subst.
    esplits; [econs; [rewrite <- (@eval_rel _ _ _ _ REGS HEAD); exact EVAL | reflexivity]|].
    exists md. splits; ss. apply regs_rel_set_opt. ss.
  - (* break *)
    inversion STACK as [| ? rmap0 rmap' r0 s_b s_c c0 ec0 REGS0 CODE_B CODE_C REST | |]; subst.
    esplits; [econs; reflexivity|].
    exists md. splits; ss.
  - (* call *)
    destruct HEAD as [(MD & es' & lab & prms' & s_f' & ES & MF & FIND' & TCODE)
                     | (prms' & s_f' & MF & FIND' & RCODE & NIN)].
    + subst md es. rewrite FIND in FIND'. inv FIND'.
      hexploit sem_exprs_snoc; eauto. intros (vs' & v_mid & VS & EVAL' & _). subst vs.
      rewrite ! app_length in ARITY. ss.
      hexploit erase_find_rw; eauto. intros [RW_F FIND_E].
      rewrite RW_F, removelast_last.
      esplits; [econs; [rewrite <- (@evals_rel true _ _ es' REGS (fun _ => MF)); exact EVAL' | exact FIND_E | lia]|].
      exists true. splits; ss.
      * apply bind_params_mid. lia.
      * eapply (@stack_fn env envt true true); [exact REGS | exact CODE' | exact STACK].
    + rewrite FIND in FIND'. inv FIND'.
      hexploit erase_find_ro; eauto. intros [RO_F FIND_E].
      rewrite RO_F.
      esplits; [econs; [rewrite <- (@evals_rel _ _ _ _ REGS MF); exact EVAL | exact FIND_E | exact ARITY]|].
      exists false. splits; ss. eapply stack_fn; [exact REGS | exact CODE' | exact STACK].
  - (* return *)
    hexploit stack_rel_pop; eauto. intros (ec_loops & ec2 & ELOOPS & (md' & rmap' & EC & REGS' & CODE2 & STACK2)).
    subst ec.
    esplits;
      [eapply EThread.step_return;
       [rewrite <- (@eval_rel _ _ _ _ REGS HEAD); exact EVAL | reflexivity | exact ELOOPS]|].
    exists md'. splits; ss. apply regs_rel_add. ss.
  - (* chkpt-call *)
    destruct HEAD as (MD & TCODE). subst md.
    esplits; [econs|].
    exists true. splits; ss. econs; ss.
  - (* chkpt-return *)
    hexploit stack_rel_pop; eauto. intros (ec_loops & ec2 & ELOOPS & (rmap' & EC & MD & REGS' & CODE2 & STACK2)).
    subst ec md.
    esplits;
      [eapply EThread.step_blk_return;
       [rewrite <- (@eval_rel _ _ _ _ REGS HEAD); exact EVAL | reflexivity | exact ELOOPS]|].
    exists true. splits; [apply regs_rel_add; exact REGS' | ss | ss | ss |].
    ss. intro m'. rewrite fun_add_spec. destruct (m' == m); ss. specialize (NR m'). lia.
  - (* chkpt-replay *)
    specialize (NR m). lia.
  - (* pcas-succ *)
    destruct HEAD as (MD & MF_L & MF_O & MF_N). subst md.
    eexists. split.
    { eapply EThread.step_cas_succ; [rewrite <- (@eval_rel true _ regs' e_loc REGS (fun _ => MF_L)); exact LOC
                                    | exact AS_LOC
                                    | rewrite <- (@eval_rel true _ regs' e_old REGS (fun _ => MF_O)); exact OLD
                                    | rewrite <- (@eval_rel true _ regs' e_new REGS (fun _ => MF_N)); exact NEW]. }
    exists true. splits; [apply regs_rel_add; exact REGS | ss | ss | ss |].
    ss. intro m'. rewrite fun_add_spec. destruct (m' == m); ss. specialize (NR m'). lia.
  - (* pcas-fail *)
    destruct HEAD as (MD & MF_L & MF_O & MF_N). subst md.
    eexists. split.
    { eapply EThread.step_cas_fail; [rewrite <- (@eval_rel true _ regs' e_loc REGS (fun _ => MF_L)); exact LOC
                                    | exact AS_LOC
                                    | rewrite <- (@eval_rel true _ regs' e_old REGS (fun _ => MF_O)); exact OLD
                                    | exact NE]. }
    exists true. splits; [apply regs_rel_add; exact REGS | ss | ss | ss |].
    ss. intro m'. rewrite fun_add_spec. destruct (m' == m); ss. specialize (NR m'). lia.
  - (* pcas-replay *)
    specialize (NR m). lia.
Qed.

Definition msim (env: Env.t) (envt: EnvType.t) (mach: Machine.t) (emach: EMachine.t) : Prop :=
  IdMap.Forall2 (fun _ thr ethr => tsim env envt thr ethr) mach.(Machine.tmap) emach.(EMachine.tmap)
  /\ mach.(Machine.mem) = emach.(EMachine.mem).

Lemma sim_rtc:
  forall p envt tr mach mach',
    TypeSystem.env_ok p.(prog_env) envt ->
    Machine.rtc Machine.normal p tr mach mach' ->
  forall emach,
    msim p.(prog_env) envt mach emach ->
  exists emach', EMachine.rtc (erase p) tr emach emach'.
Proof.
  intros p envt tr mach mach' OK RTC. induction RTC; intros emach (SIM & MEM).
  - exists emach. econs 1.
  - subst. inv ONE.
    specialize (SIM tid) as SIM_T. rewrite THR1 in SIM_T. inversion SIM_T as [|? ethr1 TSIM1 EQ1 FIND_E]. subst.
    hexploit sim_step; eauto. intros (ethr2 & ESTEP & TSIM2).
    hexploit (IHRTC (EMachine.mk (IdMap.add tid ethr2 emach.(EMachine.tmap)) mem2)).
    { split; ss. intro tid'. rewrite ! IdMap.add_spec. condtac; ss. econs. ss. }
    intros (emach' & ERTC). exists emach'.
    econs 2; [| exact ERTC | ss]. econs; eauto. rewrite <- MEM. ss.
Qed.

Lemma tmap_of_map A B (f: A -> B):
  forall ss tid k,
    IdMap.find k (tmap_of tid (map f ss)) = option_map f (IdMap.find k (tmap_of tid ss)).
Proof.
  induction ss as [|a ss IH]; ss; i.
  - rewrite ! IdMap.gempty. ss.
  - rewrite ! IdMap.add_spec. condtac; ss.
Qed.

Lemma msim_init p envt
      (OK: TypeSystem.env_ok p.(prog_env) envt)
      (TYPED: Forall (fun s => exists labs, EnvType.rw_judge envt labs s) p.(prog_threads)):
  msim p.(prog_env) envt (Machine.init p) (EMachine.init (erase p)).
Proof.
  split; ss. intro tid. rewrite ! IdMap.map_spec. unfold prog_s. rewrite tmap_of_map.
  destruct (IdMap.find tid (tmap_of BinNums.xH (prog_threads p))) as [s|] eqn:FIND; ss; econs.
  exists true. splits; ss.
  - intros r NEQ. rewrite VRegMap.add_neq; ss.
  - rewrite Forall_forall in TYPED. hexploit TYPED; [eapply prog_s_in; eauto|]. intros (labs & RW).
    eapply tcode_rw; eauto.
  - econs.
Qed.

(* Theorem 3.4 *)
Theorem erasure:
  forall p,
    TypeSystem.prog_judge p ->
  Included _ (BE p) (EB (erase p)).
Proof.
  intros p PJ b BE_B.
  apply (detectability PJ) in BE_B. destruct BE_B as (mach & RTC).
  destruct PJ as (envt & JUDGE & TYPED).
  hexploit sim_rtc;
    [apply TypeSystem.judge_env_ok; exact JUDGE | exact RTC | apply msim_init; eauto using TypeSystem.judge_env_ok |].
  intros (emach' & ERTC). exists emach'. exact ERTC.
Qed.
