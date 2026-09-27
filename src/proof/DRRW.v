Require Import EquivDec.
Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Env.
From Memento Require Import Common.
From Memento Require Import DR.
From Memento Require Import LoopSimple.

Set Implicit Arguments.

Lemma DR_RW_gen:
  forall env envt labs s,
    TypeSystem.env_ok env envt ->
    EnvType.rw_judge envt labs s ->
    (forall f prms s_f,
        IdMap.find f envt = Some FnType.RW -> IdMap.find f env = Some (prms, s_f) -> DR env s_f) ->
  DR env s.
Proof.
  intros env envt labs s OK RW FNDR. induction RW.
  - (* empty *) apply DR_stop. left. ss.
  - (* assign *) apply DR_assign.
  - (* cas *) apply DR_pcas.
  - (* chkpt *) eapply DR_chkpt; eauto.
  - (* seq *) eapply DR_seq; eauto.
  - (* if-then-else *) apply DR_ite; eauto.
  - (* loop-simple *) eapply DR_loop_simple; eauto.
  - (* loop *) eapply DR_loop; eauto.
  - (* continue *) apply DR_stop. right. right. left. esplits; eauto.
  - (* break *) apply DR_stop. right. left. esplits; eauto.
  - (* call *)
    destruct OK as [_ OK_RW]. hexploit OK_RW; eauto. intros (prms & labs' & s_f & FIND & _).
    eapply DR_call; eauto.
  - (* return *) apply DR_stop. right. right. right. esplits; [reflexivity | econs].
Qed.

(* Lemma H.26 *)
Lemma DR_RW_ind:
  forall env envt labs s,
    TypeSystem.judge env envt ->
    EnvType.rw_judge envt labs s ->
    (forall f prms s_f,
        IdMap.find f envt = Some FnType.RW -> IdMap.find f env = Some (prms, s_f) -> DR env s_f) ->
  DR env s.
Proof. i. eapply DR_RW_gen; eauto. apply TypeSystem.judge_env_ok. ss. Qed.

Lemma judge_fn_DR:
  forall env envt,
    TypeSystem.judge env envt ->
  forall env',
    (forall f x, IdMap.find f env = Some x -> IdMap.find f env' = Some x) ->
  forall f prms s_f,
    IdMap.find f envt = Some FnType.RW ->
    IdMap.find f env = Some (prms, s_f) ->
  DR env' s_f.
Proof.
  intros env envt JUDGE. induction JUDGE; intros env' INCL g prms_g s_g FN FIND.
  - rewrite IdMap.gempty in FIND. ss.
  - rewrite IdMap.add_spec in FN, FIND. destruct (g == f) as [EQ|NEQ]; ss.
    eapply IHJUDGE; eauto. intros h x FIND_H. apply INCL. rewrite IdMap.add_spec.
    destruct (h == f) as [EQ'|NEQ']; ss. inv EQ'. congr.
  - assert (INCL0: forall h x, IdMap.find h env = Some x -> IdMap.find h env' = Some x).
    { intros h x FIND_H. apply INCL. rewrite IdMap.add_spec.
      destruct (h == f) as [EQ'|NEQ']; ss. inv EQ'. congr. }
    rewrite IdMap.add_spec in FN, FIND. destruct (g == f) as [EQ|NEQ]; ss; [|eapply IHJUDGE; eauto].
    inv FIND. eapply DR_RW_gen; [| exact RW |].
    + eapply TypeSystem.env_ok_mon; [apply TypeSystem.judge_env_ok; exact JUDGE | exact INCL0].
    + intros h prms_h s_h FN_H FIND_H.
      hexploit (@TypeSystem.judge_dom env envt h JUDGE); eauto. intros (prms' & s' & FIND').
      rewrite (INCL0 _ _ FIND') in FIND_H. inv FIND_H. eapply IHJUDGE; eauto.
Qed.

(* Lemma H.23 *)
Lemma DR_RW:
  forall env envt labs s,
    TypeSystem.judge env envt ->
    EnvType.rw_judge envt labs s ->
  DR env s.
Proof.
  intros env envt labs s JUDGE RW. eapply DR_RW_ind; eauto.
  intros f prms s_f FN FIND. eapply judge_fn_DR; eauto.
Qed.

(* Lemma 3.3 *)
Lemma DR_RW_main:
  forall env envt labs s,
    TypeSystem.judge env envt ->
    EnvType.rw_judge envt labs s ->
  DR_main env s.
Proof. i. apply DR_main_DR. eapply DR_RW; eauto. Qed.
