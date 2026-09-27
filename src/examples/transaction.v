Require Import PArith.
Require Import ZArith.
Require Import NArith.
Require Import EquivDec.
Require Import Ensembles.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Order.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Env.
From Memento Require Import Detectability.

Set Implicit Arguments.

Definition transaction : list Stmt := [
  stmt_pcas 1 (expr_int 1000) expr_unit (expr_int 1) (expr_mid 1);
  stmt_pcas 2 (expr_int 1001) expr_unit (expr_int 41) (expr_mid 2);
  stmt_pcas 3 (expr_int 1002) expr_unit (expr_int 42) (expr_mid 3);
  stmt_pcas 4 (expr_int 1000) (expr_int 1) expr_unit (expr_mid 4)
].

Definition p_transaction : Program := mk_program (IdMap.empty _) [transaction].

Definition consistent_state (mem: Mem.t) : Prop :=
  mem 1000%N = Val.unit ->
  (mem 1001%N = Val.unit /\ mem 1002%N = Val.unit)
  \/ (mem 1001%N = Val.int 41 /\ mem 1002%N = Val.int 42).

Lemma transaction_rw envt:
  exists labs, EnvType.rw_judge envt labs transaction.
Proof.
  assert (PCAS: forall r el eo en lab,
             r <> mid -> midfree el -> midfree eo -> midfree en ->
             EnvType.rw_judge envt (Singleton _ lab) [stmt_pcas r el eo en (expr_mid lab)]).
  { i. econs; eauto. }
  assert (MF_INT: forall z, midfree (expr_int z)) by (intros z FREE; ss).
  assert (MF_UNIT: midfree expr_unit) by (intro FREE; ss).
  assert (DISJ: forall (lab: Label) (labs: Ensemble Label),
             ~ Ensembles.In _ labs lab -> Disjoint _ (Singleton _ lab) labs).
  { i. econs. ii. inv H0. inv H1. ss. }
  eexists. unfold transaction.
  eapply EnvType.rw_seq with (s_l := [_]) (s_r := [_; _; _]);
    [| apply PCAS; ss |
     eapply EnvType.rw_seq with (s_l := [_]) (s_r := [_; _]);
       [| apply PCAS; ss |
        eapply EnvType.rw_seq with (s_l := [_]) (s_r := [_]); [| apply PCAS; ss | apply PCAS; ss]]].
  all: apply DISJ; intro IN;
    repeat match goal with
           | [H: Ensembles.In _ (Union _ _ _) _ |- _] => inv H
           | [H: Ensembles.In _ (Singleton _ _) _ |- _] => inv H
           end.
Qed.

Definition tx_mem (k: nat) (mem: Mem.t) : Prop :=
  match k with
  | 0 => mem 1000%N = Val.unit /\ mem 1001%N = Val.unit /\ mem 1002%N = Val.unit
  | 1 => mem 1000%N = Val.int 1 /\ mem 1001%N = Val.unit /\ mem 1002%N = Val.unit
  | 2 => mem 1000%N = Val.int 1 /\ mem 1001%N = Val.int 41 /\ mem 1002%N = Val.unit
  | 3 => mem 1000%N = Val.int 1 /\ mem 1001%N = Val.int 41 /\ mem 1002%N = Val.int 42
  | _ => mem 1000%N = Val.unit /\ mem 1001%N = Val.int 41 /\ mem 1002%N = Val.int 42
  end.

Definition tx_inv (mach: Machine.t) : Prop :=
  exists k ts mmts,
    k <= 4
    /\ mach.(Machine.tmap) = IdMap.add 1%positive (Thread.mk (skipn k transaction) [] ts mmts) (IdMap.empty _)
    /\ ts.(TState.regs) mid = Some (Val.mid [])
    /\ (forall m, (mmts m).(Mmt.time) <= ts.(TState.time))
    /\ tx_mem k mach.(Machine.mem).

Lemma tx_inv_init:
  tx_inv (Machine.init p_transaction).
Proof.
  exists 0, TState.init, Mmts.init. splits; ss. lia.
Qed.

Lemma tx_inv_step tr mach mach'
      (INV: tx_inv mach)
      (STEP: Machine.normal p_transaction tr mach mach'):
  tx_inv mach'.
Proof.
  destruct INV as (k & ts & mmts & LE & TMAP & MID & NR & MEM).
  inv STEP. rewrite TMAP, IdMap.add_spec in THR1.
  destruct (tid == 1%positive) as [EQ|NEQ]; [|rewrite IdMap.gempty in THR1; ss]. inv EQ. inv THR1.
  rewrite TMAP. ss.
  destruct k as [|[|[|[|[|k]]]]]; try lia; ss; inv THR_STEP; ss;
    try (specialize (NR m); lia);
    inv LOC; inv AS_LOC; inv OLD; try inv NEW; inv MID0;
    inv MEM_STEP; inv ONE; inv RTC; des; try congr.
  all: rewrite MID in H0; inv H0.
  all: match goal with
       | |- tx_inv {| Machine.tmap := IdMap.Node _ (Some (Thread.mk ?s _ ?ts' ?mm')) _ |} =>
           exists (4 - length s), ts', mm'
       end.
  all: splits; [ss; lia | simpl; reflexivity | ss; rewrite VRegMap.add_neq; ss | |].
  all: try (intro m'; ss; rewrite fun_add_spec; destruct (m' == _); ss; specialize (NR m'); lia).
  all: ss; rewrite ! fun_add_spec; repeat condtac; ss.
Qed.

Lemma tx_inv_rtc tr mach mach'
      (RTC: Machine.rtc Machine.normal p_transaction tr mach mach')
      (INV: tx_inv mach):
  tx_inv mach'.
Proof. induction RTC; ss. apply IHRTC. eapply tx_inv_step; eauto. Qed.

Lemma tx_inv_consistent mach
      (INV: tx_inv mach):
  consistent_state mach.(Machine.mem).
Proof.
  destruct INV as (k & ts & mmts & LE & TMAP & MID & NR & MEM). unfold consistent_state.
  destruct k as [|[|[|[|k]]]]; ss; des; i; eauto; congr.
Qed.

Theorem transaction_atomic:
  forall tr mach,
    Machine.rtc Machine.step p_transaction tr (Machine.init p_transaction) mach ->
  consistent_state mach.(Machine.mem).
Proof.
  intros tr mach RUN.
  hexploit machine_remove_crashes; [| exact RUN |].
  { exists (IdMap.empty _). split; [econs | econs; [apply transaction_rw | econs]]. }
  intros (mach' & RUN' & MEM). rewrite <- MEM.
  apply tx_inv_consistent. eapply tx_inv_rtc; eauto. apply tx_inv_init.
Qed.
