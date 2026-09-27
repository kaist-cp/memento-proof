Require Import Classical_Prop.
Require ClassicalEpsilon.
Require Import Ensembles.
Require Import FunctionalExtensionality.
Require Import Lia.
Require Import ZArith.
Require Import NArith.
Require Import EquivDec.
Require Import List.
Import ListNotations.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Order.
From Memento Require Import Syntax.

Set Implicit Arguments.

Module Time.
  Include Nat.
End Time.

Module VRegMap.
  Definition t := VReg -> option Val.t.

  Definition empty : t := fun _ => None.

  Definition add (r: VReg) (v: Val.t) (rmap: t) : t := fun_add r (Some v) rmap.

  Lemma add_eq r v rmap:
    add r v rmap r = Some v.
  Proof. unfold add. apply fun_add_spec_eq. Qed.

  Lemma add_neq r r' v rmap
        (NEQ: r' <> r):
    add r v rmap r' = rmap r'.
  Proof.
    unfold add. rewrite fun_add_spec.
    destruct (r' == r) as [EQ|NEQ']; [exfalso; apply NEQ; exact EQ | reflexivity].
  Qed.

  Lemma add_add r v1 v2 rmap:
    add r v1 (add r v2 rmap) = add r v1 rmap.
  Proof.
    funext. intro x. unfold add. rewrite ! fun_add_spec. condtac; ss.
  Qed.

  Lemma add_comm r1 r2 v1 v2 rmap
        (NEQ: r1 <> r2):
    add r1 v1 (add r2 v2 rmap) = add r2 v2 (add r1 v1 rmap).
  Proof.
    funext. intro x. unfold add. rewrite ! fun_add_spec.
    destruct (x == r1) as [E1|N1]; destruct (x == r2) as [E2|N2]; try reflexivity.
    exfalso. apply NEQ. inv E1. inv E2. reflexivity.
  Qed.
End VRegMap.

Definition set_opt (r: option VReg) (v: Val.t) (rmap: VRegMap.t) : VRegMap.t :=
  match r with
  | Some r => VRegMap.add r v rmap
  | None => rmap
  end.

Fixpoint bind_params (prms: list VReg) (vs: list Val.t) : VRegMap.t :=
  match prms, vs with
  | p :: prms', v :: vs' => VRegMap.add p v (bind_params prms' vs')
  | _, _ => VRegMap.empty
  end.

Definition op_eval (op: Op) (v1 v2: Val.t) : option Val.t :=
  match op, v1, v2 with
  | op_add, Val.int z1, Val.int z2 => Some (Val.int (z1 + z2))
  | op_sub, Val.int z1, Val.int z2 => Some (Val.int (z1 - z2))
  | op_mul, Val.int z1, Val.int z2 => Some (Val.int (z1 * z2))
  | op_eq, _, _ => Some (Val.bool (if Val.eq_dec v1 v2 then true else false))
  | op_lt, Val.int z1, Val.int z2 => Some (Val.bool (Z.ltb z1 z2))
  | op_and, Val.bool b1, Val.bool b2 => Some (Val.bool (andb b1 b2))
  | op_or, Val.bool b1, Val.bool b2 => Some (Val.bool (orb b1 b2))
  | _, _, _ => None
  end.

Fixpoint sem_expr (rmap: VRegMap.t) (e: Expr) : option Val.t :=
  match e with
  | expr_unit => Some Val.unit
  | expr_int z => Some (Val.int z)
  | expr_bool b => Some (Val.bool b)
  | expr_reg r => rmap r
  | expr_op op e1 e2 =>
      match sem_expr rmap e1, sem_expr rmap e2 with
      | Some v1, Some v2 => op_eval op v1 v2
      | _, _ => None
      end
  | expr_proj e i =>
      match sem_expr rmap e with
      | Some (Val.pair v1 v2) => Some (if i then v1 else v2)
      | _ => None
      end
  | expr_pair e1 e2 =>
      match sem_expr rmap e1, sem_expr rmap e2 with
      | Some v1, Some v2 => Some (Val.pair v1 v2)
      | _, _ => None
      end
  | expr_inl e => option_map Val.inl (sem_expr rmap e)
  | expr_inr e => option_map Val.inr (sem_expr rmap e)
  | expr_match e xl el xr er =>
      match sem_expr rmap e with
      | Some (Val.inl v) => sem_expr (VRegMap.add xl v rmap) el
      | Some (Val.inr v) => sem_expr (VRegMap.add xr v rmap) er
      | _ => None
      end
  | expr_eps => Some (Val.mid [])
  | expr_lab e lab =>
      match sem_expr rmap e with
      | Some (Val.mid m) => Some (Val.mid (m ++ [lab]))
      | _ => None
      end
  end.

Fixpoint sem_exprs (rmap: VRegMap.t) (es: list Expr) : option (list Val.t) :=
  match es with
  | [] => Some []
  | e :: es' =>
      match sem_expr rmap e, sem_exprs rmap es' with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

Lemma sem_expr_mid rmap lab m
      (EVAL: sem_expr rmap (expr_mid lab) = Some (Val.mid m)):
  exists pfx, rmap mid = Some (Val.mid pfx) /\ m = pfx ++ [lab].
Proof.
  unfold expr_mid in EVAL. ss. destruct (rmap mid) as [[]|]; inv EVAL. eauto.
Qed.

Lemma sem_expr_mid_inv rmap lab v
      (EVAL: sem_expr rmap (expr_mid lab) = Some v):
  exists pfx, rmap mid = Some (Val.mid pfx) /\ v = Val.mid (pfx ++ [lab]).
Proof.
  unfold expr_mid in EVAL. ss. destruct (rmap mid) as [[]|]; inv EVAL. eauto.
Qed.

Lemma sem_exprs_snoc rmap es e vs
      (EVAL: sem_exprs rmap (es ++ [e]) = Some vs):
  exists vs' v, vs = vs' ++ [v] /\ sem_exprs rmap es = Some vs' /\ sem_expr rmap e = Some v.
Proof.
  revert vs EVAL. induction es as [|a es IH]; ss; i.
  - destruct (sem_expr rmap e) as [v|] eqn:E; inv EVAL. exists [], v. ss.
  - destruct (sem_expr rmap a) as [va|] eqn:A; ss; try by inv EVAL.
    destruct (sem_exprs rmap (es ++ [e])) as [vs0|] eqn:E; inv EVAL.
    hexploit IH; eauto. intros (vs' & v & VS & EVAL' & EVAL_E). subst.
    exists (va :: vs'), v. rewrite EVAL'. ss.
Qed.

Lemma bind_params_last prms x vs v
      (NODUP: NoDup (prms ++ [x]))
      (LEN: length prms = length vs):
  bind_params (prms ++ [x]) (vs ++ [v]) x = Some v.
Proof.
  revert vs LEN NODUP. induction prms; destruct vs; ss; i.
  - apply VRegMap.add_eq.
  - inv NODUP. rewrite VRegMap.add_neq.
    + eapply IHprms; eauto.
    + ii. subst. apply H1. apply in_or_app. right. econs. ss.
Qed.

Definition as_loc (v: Val.t) : option PLoc :=
  match v with
  | Val.int z => if Z.leb 0 z then Some (Z.to_N z) else None
  | _ => None
  end.

(* Figure 17 *)
Module Cont.
  Inductive t :=
  | loopcont (rmap: VRegMap.t) (r: option VReg) (s_body: list Stmt) (s_cont: list Stmt)
  | fncont (rmap: VRegMap.t) (r: VReg) (s_cont: list Stmt)
  | chkptcont (rmap: VRegMap.t) (r: VReg) (s_cont: list Stmt) (m: list Label)
  .

  Definition is_loop (c: t) :=
    match c with
    | loopcont _ _ _ _ => true
    | _ => false
    end.

  Definition Loops (c: list t) := Forall is_loop c.

  Lemma loops_app_distr:
    forall c1 c2,
      Loops (c1 ++ c2) <-> Loops c1 /\ Loops c2.
  Proof. apply Forall_app. Qed.

  Lemma loops_base_cont_eq:
    forall c_loops0 c_loops1 c0 c1 c_sfx0 c_sfx1,
      Loops c_loops0 ->
      Loops c_loops1 ->
      ~ Loops [c0] ->
      ~ Loops [c1] ->
      c_loops0 ++ c0 :: c_sfx0 = c_loops1 ++ c1 :: c_sfx1 ->
    c0 :: c_sfx0 = c1 :: c_sfx1.
  Proof.
    induction c_loops0 as [|x c_loops0 IH]; intros c_loops1 c0 c1 c_sfx0 c_sfx1 L0 L1 N0 N1 EQ;
      destruct c_loops1 as [|y c_loops1]; ss.
    - inv EQ. exfalso. apply N0. inversion L1 as [|? ? IS_LOOP REST]. econs; [exact IS_LOOP | econs].
    - inv EQ. exfalso. apply N1. inversion L0 as [|? ? IS_LOOP REST]. econs; [exact IS_LOOP | econs].
    - inv EQ. inversion L0 as [|? ? IS_LOOP0 L0']. inversion L1 as [|? ? IS_LOOP1 L1'].
      eapply IH; eauto.
  Qed.

  Definition seq (c: t) (s: list Stmt) :=
    match c with
    | loopcont rmap r s_body s_cont => loopcont rmap r s_body (s_cont ++ s)
    | fncont rmap r s_cont => fncont rmap r (s_cont ++ s)
    | chkptcont rmap r s_cont m => chkptcont rmap r (s_cont ++ s) m
    end.

  Fixpoint seql (cl: list t) (s: list Stmt) :=
    match cl with
    | [] => []
    | [c_base] => [seq c_base s]
    | h :: t => h :: seql t s
    end.

  Lemma seql_last:
    forall s c_pfx c_base,
      seql (c_pfx ++ [c_base]) s = c_pfx ++ [seq c_base s].
  Proof.
    i. induction c_pfx; ss.
    destruct (c_pfx ++ [c_base]) eqn:E; ss.
    { destruct c_pfx; ss. }
    rewrite IHc_pfx. ss.
  Qed.
End Cont.

(* Definition H.3 *)
Definition seq_sc_unzip (s: list Stmt) (c: list Cont.t) (s': list Stmt) :=
  match Cont.seql c s' with
  | [] => (s ++ s', [])
  | c' => (s, c')
  end.

Definition seq_sc (sc: (list Stmt * list Cont.t)) (s': list Stmt) := seq_sc_unzip (fst sc) (snd sc) s'.

Notation "sc ++₁ s'" := (seq_sc sc s') (at level 62).

Lemma seq_sc_nil:
  forall s s',
    (s, []) ++₁ s' = (s ++ s', []).
Proof. ss. Qed.

Lemma seq_sc_last:
  forall s c_pfx c_base s',
    (s, c_pfx ++ [c_base]) ++₁ s' = (s, c_pfx ++ [Cont.seq c_base s']).
Proof.
  i. unfold seq_sc, seq_sc_unzip. ss. rewrite Cont.seql_last.
  destruct (c_pfx ++ [Cont.seq c_base s']) eqn:E; ss. destruct c_pfx; ss.
Qed.

Module TState.
  Record t := mk {
    regs: VRegMap.t;
    time: Time.t;
  }.

  Definition init := mk (VRegMap.add mid (Val.mid []) VRegMap.empty) 0.
End TState.

Module Mmt.
  Record t := mk {
    val: Val.t;
    time: Time.t;
  }.
End Mmt.

Module Mmts.
  Definition t := list Label -> Mmt.t.

  Definition init : t := fun _ => Mmt.mk Val.unit 0.

  Definition mmts_in (mids: Ensemble (list Label)) (m: list Label)
    : { Ensembles.In (list Label) mids m } + { ~ Ensembles.In (list Label) mids m } :=
    ClassicalEpsilon.excluded_middle_informative (Ensembles.In (list Label) mids m).

  Definition agree_on (mids: Ensemble (list Label)) (mmts mmts': t) : Prop :=
    forall m, Ensembles.In _ mids m -> mmts m = mmts' m.

  Definition merge (mids: Ensemble (list Label)) (mmts mmts_a: t) : t :=
    fun m => if mmts_in mids m then mmts m else mmts_a m.
End Mmts.

Module Event.
  Inductive t :=
  | R (l: PLoc) (v: Val.t)
  | U (l: PLoc) (v_old v_new: Val.t)
  .
End Event.

Definition filter_updates (tr: list Event.t) : list Event.t :=
  filter (fun ev => match ev with Event.U _ _ _ => true | _ => false end) tr.

Module Thread.
  Record t := mk {
    stmt: list Stmt;
    cont: list Cont.t;
    ts: TState.t;
    mmts: Mmts.t;
  }.

  (* Figures 20 and 21 *)
  Inductive step (env: Env.t) : list Event.t -> t -> t -> Prop :=
  | step_assign
      r e s c ts mmts v
      (EVAL: sem_expr ts.(TState.regs) e = Some v)
    : step env []
        (mk (stmt_assign r e :: s) c ts mmts)
        (mk s c (TState.mk (VRegMap.add r v ts.(TState.regs)) ts.(TState.time)) mmts)
  | step_pload
      r e s c ts mmts vl l v
      (EVAL: sem_expr ts.(TState.regs) e = Some vl)
      (LOC: as_loc vl = Some l)
    : step env [Event.R l v]
        (mk (stmt_pload r e :: s) c ts mmts)
        (mk s c (TState.mk (VRegMap.add r v ts.(TState.regs)) ts.(TState.time)) mmts)
  | step_palloc
      r e s c ts mmts v l
      (EVAL: sem_expr ts.(TState.regs) e = Some v)
    : step env [Event.R l v]
        (mk (stmt_palloc r e :: s) c ts mmts)
        (mk s c (TState.mk (VRegMap.add r (Val.int (Z.of_N l)) ts.(TState.regs)) ts.(TState.time)) mmts)
  | step_branch
      e s_t s_f s c ts mmts b
      (EVAL: sem_expr ts.(TState.regs) e = Some (Val.bool b))
    : step env []
        (mk (stmt_if e s_t s_f :: s) c ts mmts)
        (mk ((if b then s_t else s_f) ++ s) c ts mmts)
  | step_loop
      r e s_body s c ts mmts v
      (EVAL: sem_expr ts.(TState.regs) e = Some v)
    : step env []
        (mk (stmt_loop r e s_body :: s) c ts mmts)
        (mk s_body (Cont.loopcont ts.(TState.regs) r s_body s :: c)
            (TState.mk (set_opt r v ts.(TState.regs)) ts.(TState.time)) mmts)
  | step_continue
      e s c ts mmts v rmap r s_body s_cont c'
      (EVAL: sem_expr ts.(TState.regs) e = Some v)
      (CONT: c = Cont.loopcont rmap r s_body s_cont :: c')
    : step env []
        (mk (stmt_continue e :: s) c ts mmts)
        (mk s_body c (TState.mk (set_opt r v rmap) ts.(TState.time)) mmts)
  | step_break
      s c ts mmts rmap r s_body s_cont c'
      (CONT: c = Cont.loopcont rmap r s_body s_cont :: c')
    : step env []
        (mk (stmt_break :: s) c ts mmts)
        (mk s_cont c' (TState.mk rmap ts.(TState.time)) mmts)
  | step_call
      r f es s c ts mmts vs prms s_f
      (EVAL: sem_exprs ts.(TState.regs) es = Some vs)
      (FIND: IdMap.find f env = Some (prms, s_f))
      (ARITY: length prms = length vs)
    : step env []
        (mk (stmt_call r f es :: s) c ts mmts)
        (mk s_f (Cont.fncont ts.(TState.regs) r s :: c)
            (TState.mk (bind_params prms vs) ts.(TState.time)) mmts)
  | step_return
      e s c ts mmts v c_loops rmap r s2 c2
      (EVAL: sem_expr ts.(TState.regs) e = Some v)
      (CONT: c = c_loops ++ Cont.fncont rmap r s2 :: c2)
      (LOOPS: Cont.Loops c_loops)
    : step env []
        (mk (stmt_return e :: s) c ts mmts)
        (mk s2 c2 (TState.mk (VRegMap.add r v rmap) ts.(TState.time)) mmts)
  | step_chkpt_call
      r s_c e_mid s c ts mmts m
      (EVAL: sem_expr ts.(TState.regs) e_mid = Some (Val.mid m))
      (TIME: (mmts m).(Mmt.time) <= ts.(TState.time))
    : step env []
        (mk (stmt_chkpt r s_c e_mid :: s) c ts mmts)
        (mk s_c (Cont.chkptcont ts.(TState.regs) r s m :: c) ts mmts)
  | step_chkpt_return
      e s c ts mmts v c_loops rmap r s2 m c2 t
      (EVAL: sem_expr ts.(TState.regs) e = Some v)
      (CONT: c = c_loops ++ Cont.chkptcont rmap r s2 m :: c2)
      (LOOPS: Cont.Loops c_loops)
      (TIME: ts.(TState.time) < t)
    : step env []
        (mk (stmt_return e :: s) c ts mmts)
        (mk s2 c2 (TState.mk (VRegMap.add r v rmap) t) (fun_add m (Mmt.mk v t) mmts))
  | step_chkpt_replay
      r s_c e_mid s c ts mmts m
      (EVAL: sem_expr ts.(TState.regs) e_mid = Some (Val.mid m))
      (TIME: ts.(TState.time) < (mmts m).(Mmt.time))
    : step env []
        (mk (stmt_chkpt r s_c e_mid :: s) c ts mmts)
        (mk s c (TState.mk (VRegMap.add r (mmts m).(Mmt.val) ts.(TState.regs)) (mmts m).(Mmt.time)) mmts)
  | step_pcas_succ
      r e_loc e_old e_new e_mid s c ts mmts vl l v_old v_new m t
      (LOC: sem_expr ts.(TState.regs) e_loc = Some vl)
      (AS_LOC: as_loc vl = Some l)
      (OLD: sem_expr ts.(TState.regs) e_old = Some v_old)
      (NEW: sem_expr ts.(TState.regs) e_new = Some v_new)
      (MID: sem_expr ts.(TState.regs) e_mid = Some (Val.mid m))
      (TIME_MMT: (mmts m).(Mmt.time) <= ts.(TState.time))
      (TIME: ts.(TState.time) < t)
    : step env [Event.U l v_old v_new]
        (mk (stmt_pcas r e_loc e_old e_new e_mid :: s) c ts mmts)
        (mk s c (TState.mk (VRegMap.add r (Val.pair (Val.bool true) v_old) ts.(TState.regs)) t)
            (fun_add m (Mmt.mk (Val.pair (Val.bool true) v_old) t) mmts))
  | step_pcas_fail
      r e_loc e_old e_new e_mid s c ts mmts vl l v_old v m t
      (LOC: sem_expr ts.(TState.regs) e_loc = Some vl)
      (AS_LOC: as_loc vl = Some l)
      (OLD: sem_expr ts.(TState.regs) e_old = Some v_old)
      (MID: sem_expr ts.(TState.regs) e_mid = Some (Val.mid m))
      (NE: v <> v_old)
      (TIME_MMT: (mmts m).(Mmt.time) <= ts.(TState.time))
      (TIME: ts.(TState.time) < t)
    : step env [Event.R l v]
        (mk (stmt_pcas r e_loc e_old e_new e_mid :: s) c ts mmts)
        (mk s c (TState.mk (VRegMap.add r (Val.pair (Val.bool false) v) ts.(TState.regs)) t)
            (fun_add m (Mmt.mk (Val.pair (Val.bool false) v) t) mmts))
  | step_pcas_replay
      r e_loc e_old e_new e_mid s c ts mmts m
      (MID: sem_expr ts.(TState.regs) e_mid = Some (Val.mid m))
      (TIME: ts.(TState.time) < (mmts m).(Mmt.time))
    : step env []
        (mk (stmt_pcas r e_loc e_old e_new e_mid :: s) c ts mmts)
        (mk s c (TState.mk (VRegMap.add r (mmts m).(Mmt.val) ts.(TState.regs)) (mmts m).(Mmt.time)) mmts)
  .

  (* Definition H.9 *)
  Inductive step_base_cont (env: Env.t) (c: list Cont.t) (tr: list Event.t) (thr1 thr2: t): Prop :=
  | step_base_cont_intro
      c'
      (NORMAL_STEP: step env tr thr1 thr2)
      (BASE: thr2.(cont) = c' ++ c)
  .

  (* Definition H.1 *)
  Inductive rtc (env: Env.t) (c: list Cont.t) : list Event.t -> t -> t -> Prop :=
  | rtc_refl
      thr
    : rtc env c [] thr thr
  | rtc_tc
      tr tr0 tr1 thr thr0 thr_term
      (ONE: step_base_cont env c tr0 thr thr0)
      (RTC: rtc env c tr1 thr0 thr_term)
      (TRACE: tr = tr0 ++ tr1)
    : rtc env c tr thr thr_term
  .

  (* Definition H.2 *)
  Inductive tc (env: Env.t) (c: list Cont.t) : list Event.t -> t -> t -> Prop :=
  | tc_intro
      tr tr0 tr1 thr thr0 thr_term
      (ONE: step_base_cont env c tr0 thr thr0)
      (RTC: rtc env c tr1 thr0 thr_term)
      (TRACE: tr = tr0 ++ tr1)
    : tc env c tr thr thr_term
  .

  Inductive stepE (env: Env.t) (s_init: list Stmt) : list Event.t -> t -> t -> Prop :=
  | stepE_step
      tr thr1 thr2
      (STEP: step env tr thr1 thr2)
    : stepE env s_init tr thr1 thr2
  | stepE_crash
      thr1
    : stepE env s_init [] thr1 (mk s_init [] TState.init thr1.(mmts))
  .

  Inductive rtcE (env: Env.t) (s_init: list Stmt) : list Event.t -> t -> t -> Prop :=
  | rtcE_refl
      thr
    : rtcE env s_init [] thr thr
  | rtcE_tc
      tr tr0 tr1 thr thr0 thr_term
      (ONE: stepE env s_init tr0 thr thr0)
      (RTC: rtcE env s_init tr1 thr0 thr_term)
      (TRACE: tr = tr0 ++ tr1)
    : rtcE env s_init tr thr thr_term
  .

  Lemma rtc_trans:
    forall env tr1 thr1 thr2 c tr2 thr3,
      rtc env c tr1 thr1 thr2 ->
      rtc env c tr2 thr2 thr3 ->
    rtc env c (tr1 ++ tr2) thr1 thr3.
  Proof.
    i. revert H0. revert thr3 tr2.
    induction H.
    { subst. i. rewrite app_nil_l. ss. }
    i. subst.
    hexploit IHrtc; eauto. i.
    econs 2; eauto. rewrite app_assoc. ss.
  Qed.

  Lemma step_time:
    forall env tr thr1 thr2,
      step env tr thr1 thr2 ->
    thr1.(ts).(TState.time) <= thr2.(ts).(TState.time).
  Proof. i. inv H; ss; lia. Qed.

  (* Lemma H.14 *)
  Lemma step_time_mon:
    forall env c tr thr thr_term,
      rtc env c tr thr thr_term ->
    thr.(ts).(TState.time) <= thr_term.(ts).(TState.time).
  Proof.
    i. induction H; ss.
    inv ONE. hexploit step_time; eauto. lia.
  Qed.
End Thread.

(* Figure 19 *)
Module Mem.
  Definition t := PLoc -> Val.t.

  Definition init : t := fun _ => Val.unit.

  Inductive step : list Event.t -> t -> t -> Prop :=
  | step_read
      mem l v
      (GET: mem l = v)
    : step [Event.R l v] mem mem
  | step_update
      mem l v_old v_new
      (GET: mem l = v_old)
    : step [Event.U l v_old v_new] mem (fun_add l v_new mem)
  .

  Inductive rtc : list Event.t -> t -> t -> Prop :=
  | rtc_refl
      mem
    : rtc [] mem mem
  | rtc_step
      ev tr mem0 mem1 mem2
      (ONE: step [ev] mem0 mem1)
      (RTC: rtc tr mem1 mem2)
    : rtc (ev :: tr) mem0 mem2
  .
End Mem.

Fixpoint tmap_of A (tid: positive) (ss: list A) : IdMap.t A :=
  match ss with
  | [] => IdMap.empty _
  | s :: ss' => IdMap.add tid s (tmap_of (Pos.succ tid) ss')
  end.

Definition prog_s (p: Program) : IdMap.t (list Stmt) := tmap_of 1 p.(prog_threads).

(* Figure 18 *)
Module Machine.
  Record t := mk {
    tmap: IdMap.t Thread.t;
    mem: Mem.t;
  }.

  Definition init_thread (s: list Stmt): Thread.t :=
    Thread.mk s [] TState.init Mmts.init.

  Definition init (p: Program): t :=
    mk (IdMap.map init_thread (prog_s p)) Mem.init.

  Lemma init_find p tid:
    IdMap.find tid (init p).(tmap) = option_map init_thread (IdMap.find tid (prog_s p)).
  Proof. apply IdMap.map_spec. Qed.

  Inductive normal (p: Program) (tr: list Event.t) (mach1 mach2: t): Prop :=
  | normal_intro
      tid thr1 thr2 tr_t mem2
      (THR1: IdMap.find tid mach1.(tmap) = Some thr1)
      (THR_STEP: Thread.step p.(prog_env) tr_t thr1 thr2)
      (MEM_STEP: Mem.rtc tr_t mach1.(mem) mem2)
      (TRACE: tr = filter_updates tr_t)
      (MACHINE2: mach2 = mk (IdMap.add tid thr2 mach1.(tmap)) mem2)
  .

  Inductive crash (p: Program) (tr: list Event.t) (mach1 mach2: t): Prop :=
  | crash_intro
      tid s thr1
      (TRACE: tr = [])
      (STMT: IdMap.find tid (prog_s p) = Some s)
      (THR1: IdMap.find tid mach1.(tmap) = Some thr1)
      (MACHINE2: mach2 = mk (IdMap.add tid (Thread.mk s [] TState.init thr1.(Thread.mmts)) mach1.(tmap)) mach1.(mem))
  .

  Inductive step (p: Program) (tr: list Event.t) (mach1 mach2: t): Prop :=
  | step_normal
      (STEP: normal p tr mach1 mach2)
  | step_crash
      (STEP: crash p tr mach1 mach2)
  .

  Inductive rtc (step: Program -> list Event.t -> t -> t -> Prop) (p: Program) : list Event.t -> t -> t -> Prop :=
  | rtc_refl
      mach
    : rtc step p [] mach mach
  | rtc_tc
      tr tr0 tr1 mach mach0 mach_term
      (ONE: step p tr0 mach mach0)
      (RTC: rtc step p tr1 mach0 mach_term)
      (TRACE: tr = tr0 ++ tr1)
    : rtc step p tr mach mach_term
  .
End Machine.
