Require Import List.
Import ListNotations.
Require Import Ensembles.
Require Import EquivDec.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.

Set Implicit Arguments.

Module FnType.
  Inductive t :=
  | RO
  | RW
  .
End FnType.

(* Figure 22 *)
Module EnvType.
  Definition t := IdMap.t FnType.t.

  Inductive ro_judge (envt: t) : list Stmt -> Prop :=
  | ro_empty
    : ro_judge envt []
  | ro_assign
      r e
    : ro_judge envt [stmt_assign r e]
  | ro_load
      r e
    : ro_judge envt [stmt_pload r e]
  | ro_alloc
      r e
    : ro_judge envt [stmt_palloc r e]
  | ro_loop
      r e s
      (BODY: ro_judge envt s)
    : ro_judge envt [stmt_loop r e s]
  | ro_continue
      e
    : ro_judge envt [stmt_continue e]
  | ro_break
    : ro_judge envt [stmt_break]
  | ro_call
      r f es
      (FN: IdMap.find f envt = Some FnType.RO)
    : ro_judge envt [stmt_call r f es]
  | ro_return
      e
    : ro_judge envt [stmt_return e]
  | ro_seq
      s_l s_r
      (LEFT: ro_judge envt s_l)
      (RIGHT: ro_judge envt s_r)
    : ro_judge envt (s_l ++ s_r)
  | ro_ite
      e s_t s_f
      (TRUE: ro_judge envt s_t)
      (FALSE: ro_judge envt s_f)
    : ro_judge envt [stmt_if e s_t s_f]
  .

  Inductive rw_judge (envt: t) : Ensemble Label -> list Stmt -> Prop :=
  | rw_empty
    : rw_judge envt (Empty_set _) []
  | rw_assign
      r e
      (NMID: r <> mid)
      (MF: midfree e)
    : rw_judge envt (Empty_set _) [stmt_assign r e]
  | rw_cas
      r e_loc e_old e_new lab
      (NMID: r <> mid)
      (MF_LOC: midfree e_loc)
      (MF_OLD: midfree e_old)
      (MF_NEW: midfree e_new)
    : rw_judge envt (Singleton _ lab) [stmt_pcas r e_loc e_old e_new (expr_mid lab)]
  | rw_chkpt
      r s lab
      (RO: ro_judge envt s)
      (NMID: r <> mid)
      (MF: midfree_stmts s)
    : rw_judge envt (Singleton _ lab) [stmt_chkpt r s (expr_mid lab)]
  | rw_seq
      labs_l labs_r s_l s_r
      (DISJ: Disjoint _ labs_l labs_r)
      (LEFT: rw_judge envt labs_l s_l)
      (RIGHT: rw_judge envt labs_r s_r)
    : rw_judge envt (Union _ labs_l labs_r) (s_l ++ s_r)
  | rw_ite
      labs_t labs_f e s_t s_f
      (TRUE: rw_judge envt labs_t s_t)
      (FALSE: rw_judge envt labs_f s_f)
      (MF: midfree e)
    : rw_judge envt (Union _ labs_t labs_f) [stmt_if e s_t s_f]
  | rw_loop_simple
      labs s
      (BODY: rw_judge envt labs s)
    : rw_judge envt labs [stmt_loop None expr_unit s]
  | rw_loop
      labs r e lab s
      (BODY: rw_judge envt labs s)
      (NIN: ~ Ensembles.In _ labs lab)
      (NMID: r <> mid)
      (MF: midfree e)
    : rw_judge envt (Union _ (Singleton _ lab) labs)
        [stmt_loop (Some r) e (stmt_chkpt r [stmt_return (expr_reg r)] (expr_mid lab) :: s)]
  | rw_continue
      e
      (MF: midfree e)
    : rw_judge envt (Empty_set _) [stmt_continue e]
  | rw_break
    : rw_judge envt (Empty_set _) [stmt_break]
  | rw_call
      r f es lab
      (FN: IdMap.find f envt = Some FnType.RW)
      (NMID: r <> mid)
      (MF: Forall midfree es)
    : rw_judge envt (Singleton _ lab) [stmt_call r f (es ++ [expr_mid lab])]
  | rw_return
      e
      (MF: midfree e)
    : rw_judge envt (Empty_set _) [stmt_return e]
  .

  Definition incl (envt envt': t) : Prop :=
    forall f ty, IdMap.find f envt = Some ty -> IdMap.find f envt' = Some ty.

  Lemma ro_judge_mon envt envt' s
        (INCL: incl envt envt')
        (RO: ro_judge envt s):
    ro_judge envt' s.
  Proof. induction RO; econs; eauto. Qed.

  Lemma rw_judge_mon envt envt' labs s
        (INCL: incl envt envt')
        (RW: rw_judge envt labs s):
    rw_judge envt' labs s.
  Proof. induction RW; econs; eauto using ro_judge_mon. Qed.
End EnvType.

Lemma included_refl U (A: Ensemble U): Included _ A A.
Proof. ii. ss. Qed.

Lemma included_trans U (A B C: Ensemble U):
  Included _ A B -> Included _ B C -> Included _ A C.
Proof. ii. eauto. Qed.

Lemma included_union_l U (A B: Ensemble U): Included _ A (Union _ A B).
Proof. ii. left. ss. Qed.

Lemma included_union_r U (A B: Ensemble U): Included _ B (Union _ A B).
Proof. ii. right. ss. Qed.

Lemma disjoint_in U (A B: Ensemble U) x:
  Disjoint _ A B -> Ensembles.In _ A x -> Ensembles.In _ B x -> False.
Proof. i. inv H. eapply H2. econs; eauto. Qed.

Lemma list_unit_app A (x: A) s1 s2:
  [x] = s1 ++ s2 -> (s1 = [] /\ s2 = [x]) \/ (s1 = [x] /\ s2 = []).
Proof. i. symmetry in H. apply app_eq_unit in H. des; subst; eauto. Qed.

Module EnvShape.
  Import EnvType.

  Definition ro_shape (envt: EnvType.t) (x: Stmt) : Prop :=
    match x with
    | stmt_assign _ _ | stmt_pload _ _ | stmt_palloc _ _
    | stmt_continue _ | stmt_break | stmt_return _ => True
    | stmt_loop _ _ s => ro_judge envt s
    | stmt_call _ f _ => IdMap.find f envt = Some FnType.RO
    | stmt_if _ s_t s_f => ro_judge envt s_t /\ ro_judge envt s_f
    | stmt_chkpt _ _ _ | stmt_pcas _ _ _ _ _ => False
    end.

  Definition rw_shape (envt: EnvType.t) (labs: Ensemble Label) (x: Stmt) : Prop :=
    match x with
    | stmt_assign r e => r <> mid /\ midfree e
    | stmt_pcas r el eo en em =>
        exists lab, em = expr_mid lab /\ Ensembles.In _ labs lab
               /\ r <> mid /\ midfree el /\ midfree eo /\ midfree en
    | stmt_chkpt r s em =>
        exists lab, em = expr_mid lab /\ Ensembles.In _ labs lab
               /\ ro_judge envt s /\ r <> mid /\ midfree_stmts s
    | stmt_if e s_t s_f =>
        exists labs_t labs_f, rw_judge envt labs_t s_t /\ rw_judge envt labs_f s_f
                         /\ Included _ labs_t labs /\ Included _ labs_f labs /\ midfree e
    | stmt_loop None e s =>
        e = expr_unit /\ exists labs', rw_judge envt labs' s /\ Included _ labs' labs
    | stmt_loop (Some r) e s =>
        exists lab labs' s', s = stmt_chkpt r [stmt_return (expr_reg r)] (expr_mid lab) :: s'
                        /\ rw_judge envt labs' s' /\ ~ Ensembles.In _ labs' lab
                        /\ Ensembles.In _ labs lab /\ Included _ labs' labs
                        /\ r <> mid /\ midfree e
    | stmt_continue e | stmt_return e => midfree e
    | stmt_break => True
    | stmt_call r f es =>
        exists es' lab, es = es' ++ [expr_mid lab] /\ IdMap.find f envt = Some FnType.RW
                   /\ Ensembles.In _ labs lab /\ r <> mid /\ Forall midfree es'
    | stmt_pload _ _ | stmt_palloc _ _ => False
    end.

  Lemma rw_shape_mon envt labs labs' x
        (INCL: Included _ labs labs')
        (SHAPE: rw_shape envt labs x):
    rw_shape envt labs' x.
  Proof.
    destruct x as [r e|r e|r e|e s_t s_f|[r|] e s|e| |r f es|e|r s e_mid|r el eo en em];
      ss; des; subst; esplits; eauto using included_trans.
  Qed.

  Lemma ro_judge_single envt x
        (RO: ro_judge envt [x]):
    ro_shape envt x.
  Proof.
    remember [x] as s eqn:S. revert x S.
    induction RO; intros x0 S; try (inv S; ss; eauto; fail).
    symmetry in S. apply list_unit_app in S. destruct S as [[L R] | [L R]]; subst; eauto.
  Qed.

  Lemma rw_judge_single envt labs x
        (RW: rw_judge envt labs [x]):
    rw_shape envt labs x.
  Proof.
    remember [x] as s eqn:S. revert x S.
    induction RW; intros x0 S.
    - inv S.
    - inv S. ss.
    - inv S. ss. esplits; eauto. econs.
    - inv S. ss. esplits; eauto. econs.
    - symmetry in S. apply list_unit_app in S. destruct S as [[L R] | [L R]]; subst.
      + eapply rw_shape_mon; [apply included_union_r | eauto].
      + eapply rw_shape_mon; [apply included_union_l | eauto].
    - inv S. ss. esplits; eauto using included_union_l, included_union_r.
    - inv S. ss. esplits; eauto. apply included_refl.
    - inv S. ss. esplits; eauto. { left. econs. } apply included_union_r.
    - inv S. ss.
    - inv S. ss.
    - inv S. ss. esplits; eauto. econs.
    - inv S. ss.
  Qed.
  Lemma ro_judge_forall envt s:
    ro_judge envt s <-> Forall (fun x => ro_judge envt [x]) s.
  Proof.
    split.
    - induction 1; try (econs; [econs; eauto | econs]; fail).
      + econs.
      + apply Forall_app. split; ss.
    - intro FA. induction FA as [|x l X FA' IH].
      + econs.
      + change (x :: l) with ([x] ++ l). eapply ro_seq; eauto.
  Qed.

  Lemma rw_judge_forall envt labs s
        (RW: rw_judge envt labs s):
    Forall (fun x => exists labs', Included _ labs' labs /\ rw_judge envt labs' [x]) s.
  Proof.
    induction RW; try (econs; [esplits; [apply included_refl | econs; eauto] | econs]; fail).
    - econs.
    - apply Forall_app. split.
      + eapply Forall_impl; [|exact IHRW1]. intros x (labs' & INCL & RW').
        exists labs'. split; [|exact RW']. eapply included_trans; [exact INCL | apply included_union_l].
      + eapply Forall_impl; [|exact IHRW2]. intros x (labs' & INCL & RW').
        exists labs'. split; [|exact RW']. eapply included_trans; [exact INCL | apply included_union_r].
  Qed.

End EnvShape.

Module TypeSystem.
  Inductive judge : Env.t -> EnvType.t -> Prop :=
  | env_empty
    : judge (IdMap.empty _) (IdMap.empty _)
  | env_ro
      env envt f prms s
      (JUDGE: judge env envt)
      (RO: EnvType.ro_judge envt s)
      (FRESH: IdMap.find f env = None)
      (NODUP: NoDup prms)
      (NMID: ~ List.In mid prms)
    : judge (IdMap.add f (prms, s) env) (IdMap.add f FnType.RO envt)
  | env_rw
      env envt f prms labs s
      (JUDGE: judge env envt)
      (RW: EnvType.rw_judge envt labs s)
      (FRESH: IdMap.find f env = None)
      (NODUP: NoDup (prms ++ [mid]))
    : judge (IdMap.add f (prms ++ [mid], s) env) (IdMap.add f FnType.RW envt)
  .

  Definition prog_judge (p: Program) : Prop :=
    exists envt,
      judge p.(prog_env) envt
      /\ Forall (fun s => exists labs, EnvType.rw_judge envt labs s) p.(prog_threads).

  Lemma judge_none env envt f
        (JUDGE: judge env envt):
    IdMap.find f env = None <-> IdMap.find f envt = None.
  Proof.
    induction JUDGE; ss.
    - rewrite ! IdMap.gempty. ss.
    - rewrite ! IdMap.add_spec. destruct (f == f0); ss.
    - rewrite ! IdMap.add_spec. destruct (f == f0); ss.
  Qed.

  (* Lemma H.15 *)
  Lemma judge_dom env envt f
        (JUDGE: judge env envt)
        (DOM: exists ty, IdMap.find f envt = Some ty):
    exists prms s_f, IdMap.find f env = Some (prms, s_f).
  Proof.
    destruct (IdMap.find f env) as [[prms s_f]|] eqn:FIND; eauto.
    apply (judge_none f JUDGE) in FIND. des. congr.
  Qed.

  Definition env_ok (env: Env.t) (envt: EnvType.t) : Prop :=
    (forall f, IdMap.find f envt = Some FnType.RO ->
       exists prms s, IdMap.find f env = Some (prms, s)
                 /\ EnvType.ro_judge envt s /\ NoDup prms /\ ~ List.In mid prms)
    /\ (forall f, IdMap.find f envt = Some FnType.RW ->
         exists prms labs s, IdMap.find f env = Some (prms ++ [mid], s)
                        /\ EnvType.rw_judge envt labs s /\ NoDup (prms ++ [mid])).

  Lemma env_ok_mon env env' envt
        (OK: env_ok env envt)
        (INCL: forall f x, IdMap.find f env = Some x -> IdMap.find f env' = Some x):
    env_ok env' envt.
  Proof.
    destruct OK as [OK_RO OK_RW]. split.
    - i. hexploit OK_RO; eauto. i. des. esplits; eauto.
    - i. hexploit OK_RW; eauto. i. des. esplits; eauto.
  Qed.

  Lemma add_incl env envt f ty
        (JUDGE: judge env envt)
        (FRESH: IdMap.find f env = None):
    EnvType.incl envt (IdMap.add f ty envt).
  Proof.
    intros f0 ty0 FIND. rewrite IdMap.add_spec. destruct (f0 == f) as [EQ|NEQ]; ss.
    inv EQ. apply (judge_none f JUDGE) in FRESH. congr.
  Qed.

  Lemma judge_env_ok env envt
        (JUDGE: judge env envt):
    env_ok env envt.
  Proof.
    induction JUDGE.
    - split; i; rewrite IdMap.gempty in *; ss.
    - hexploit (@add_incl env envt f FnType.RO); eauto. intro INCL.
      destruct IHJUDGE as [OK_RO OK_RW]. split; intros f0 FIND; rewrite ! IdMap.add_spec in *.
      + destruct (f0 == f) as [EQ|NEQ].
        * inv FIND. esplits; eauto. eapply EnvType.ro_judge_mon; eauto.
        * hexploit OK_RO; eauto. i. des. esplits; eauto. eapply EnvType.ro_judge_mon; eauto.
      + destruct (f0 == f) as [EQ|NEQ]; ss.
        hexploit OK_RW; eauto. i. des. esplits; eauto. eapply EnvType.rw_judge_mon; eauto.
    - hexploit (@add_incl env envt f FnType.RW); eauto. intro INCL.
      destruct IHJUDGE as [OK_RO OK_RW]. split; intros f0 FIND; rewrite ! IdMap.add_spec in *.
      + destruct (f0 == f) as [EQ|NEQ]; ss.
        hexploit OK_RO; eauto. i. des. esplits; eauto. eapply EnvType.ro_judge_mon; eauto.
      + destruct (f0 == f) as [EQ|NEQ].
        * inv FIND. esplits; eauto. eapply EnvType.rw_judge_mon; eauto.
        * hexploit OK_RW; eauto. i. des. esplits; eauto. eapply EnvType.rw_judge_mon; eauto.
  Qed.
End TypeSystem.
