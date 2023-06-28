Require Import PArith.
Require Import ZArith.
Require Import List.
Require RelationClasses.
Import ListNotations.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Env.
From Memento Require Import DR.

(*
  A simple transaction program:
  ```
  // Initially, EDIT = X = Y = 0
  EDIT = 1; // locked for atomicity guarantee
  X = 41
  Y = 42
  EDIT = 0;
  ```

  which is implemented as:
  r0 := pcas(loc_1000, val_0, val_1, mid_0)
  r1 := pcas(loc_1001, val_0, val_41, mid_1)
  r2 := pcas(loc_1002, val_0, val_42, mid_2)
  r0 := pcas(loc_1000, val_1, val_0, mid_3)
*)
Definition transaction := [
  (stmt_pcas
    (Pos.of_nat 0)
    (expr_reg (Pos.of_nat 1000))
    (expr_const (Val.int 0%Z))
    (expr_const (Val.int 1%Z))
    0
  );
  (stmt_pcas
    (Pos.of_nat 1)
    (expr_reg (Pos.of_nat 1001))
    (expr_const (Val.int 0%Z))
    (expr_const (Val.int 41%Z))
    1
  );
  (stmt_pcas
    (Pos.of_nat 2)
    (expr_reg (Pos.of_nat 1002))
    (expr_const (Val.int 0%Z))
    (expr_const (Val.int 42%Z))
    2
  );
  (stmt_pcas
    (Pos.of_nat 3)
    (expr_reg (Pos.of_nat 1000))
    (expr_const (Val.int 1%Z))
    (expr_const (Val.int 0%Z))
    3
  )
].

Definition consistent_state (mem: Mem.t) :=
  mem (PLoc.int 1000) = Val.int 0 ->
  (mem (PLoc.int 1001) = Val.int 0 /\ mem (PLoc.int 1002) = Val.int 0)
  \/ (mem (PLoc.int 1001) = Val.int 41 /\ mem (PLoc.int 1002) = Val.int 42).

Lemma transaction_rw:
  forall envt,
    exists labs, EnvType.rw_judge envt labs transaction.
Proof.
  i. unfold transaction. esplits.
  econs 10; cycle 4.
  { instantiate (2 := [_]). instantiate (1 := [_; _; _]). ss. }
  all: cycle 1.
  { econs 6; eauto. }
  { econs 10; cycle 4.
    { instantiate (2 := [_]). instantiate (1 := [_; _]). ss. }
    all: cycle 1.
    { econs 6; eauto. }
    { econs 10; cycle 4.
      { instantiate (2 := [_]). instantiate (1 := [_]). ss. }
      all: cycle 1.
      { econs 6; eauto. }
      { econs 10; cycle 4.
        { rewrite app_nil_l. ss. }
        all: cycle 1.
        { econs; eauto. }
        { econs 6; eauto. }
        { ss. }
        econs. ii. inv H. ss.
      }
      ss.
      econs. ii.
      inv H. inv H1; ss.
      inv H0. inv H.
    }
    ss.
    econs. ii.
    inv H. inv H1.
    { inv H0. inv H. }
    inv H; ss.
    inv H0. inv H1.
  }
  ss.
  econs. ii.
  inv H. inv H1.
  { inv H0. inv H. }
  inv H.
  { inv H0. inv H1. }
  inv H1.
  { inv H0. inv H. }
  inv H0. inv H.
Qed.

(* TODO: durability 증명할 때 필요. terminated 됐을 때 0 41 42가 있어야 함 *)
Lemma transaction_DR:
  forall env envt,
    TypeSystem.judge env envt ->
  DR env transaction.
Proof.
  i. hexploit transaction_rw. i. des.
  eapply DR_RW; eauto.
  admit. (* DR trivial lemma *)
Qed.

Lemma transaction_atomic_step:
  forall p envt s c ts mmts tr mach mach_term,
    p = prog_intro envt (IdMap.add (Pos.of_nat 1) transaction (IdMap.empty _)) ->
    IdMap.find (Pos.of_nat 1) mach.(Machine.tmap) = Some (Thread.mk s c ts mmts) ->
    suffix_of s transaction ->
    consistent_state mach.(Machine.mem) ->
    Machine.step p tr mach mach_term ->
  consistent_state mach_term.(Machine.mem).
Proof.
  admit.
Qed.

Lemma transaction_atomic_rtc_step:
  forall p envt s c ts mmts tr mach mach_term,
    p = prog_intro envt (IdMap.add (Pos.of_nat 1) transaction (IdMap.empty _)) ->
    IdMap.find (Pos.of_nat 1) mach.(Machine.tmap) = Some (Thread.mk s c ts mmts) ->
    suffix_of s transaction ->
    consistent_state mach.(Machine.mem) ->
    Machine.rtc p tr mach mach_term ->
  consistent_state mach_term.(Machine.mem).
Proof.
  i. revert envt s c ts mmts H2 H1 H0 H. induction H3; i; [ ss |]. subst.
  hexploit Machine.step_suffix_of_prog; eauto.
  { admit. }
  intro SUFFIX.

  hexploit transaction_atomic_step; eauto. i.

  specialize (SUFFIX (Pos.of_nat 1)).
  inv SUFFIX. destruct (Machine.tmap mach0); ss. subst. destruct b.
  eapply IHrtc; eauto.
Qed.

Theorem transaction_atomic:
  forall p envt tr mach_term,
    p = prog_intro envt (IdMap.add (Pos.of_nat 1) transaction (IdMap.empty _)) ->
    Machine.rtc p tr (Machine.init p) mach_term ->
  consistent_state mach_term.(Machine.mem).
Proof.
  i.
  assert (INIT_CONST: consistent_state (Machine.init p).(Machine.mem)).
  { left. ss. }
  subst.
  eapply transaction_atomic_rtc_step; eauto; [econs | refl].
Qed.
