Require Import PArith.
Require Import ZArith.
Require Import EquivDec.
Require Import List.
Require Import FunctionalExtensionality.
Require RelationClasses.
Import ListNotations.
Require Import Lia.

Require Import HahnList.
Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Order.
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
    (Pos.of_nat 1)
    (expr_const (Val.int 1000))
    (expr_const (Val.int 0%Z))
    (expr_const (Val.int 1%Z))
    1
  );
  (stmt_pcas
    (Pos.of_nat 2)
    (expr_const (Val.int 1001))
    (expr_const (Val.int 0%Z))
    (expr_const (Val.int 41%Z))
    2
  );
  (stmt_pcas
    (Pos.of_nat 3)
    (expr_const (Val.int 1002))
    (expr_const (Val.int 0%Z))
    (expr_const (Val.int 42%Z))
    3
  );
  (stmt_pcas
    (Pos.of_nat 4)
    (expr_const (Val.int 1000))
    (expr_const (Val.int 1%Z))
    (expr_const (Val.int 0%Z))
    4
  )
].

Definition consistent_state (mem: Mem.t) :=
  mem (PLoc.int 1000) = Val.int 0
  ->
  (
    mem (PLoc.int 1001) = Val.int 0 /\
    mem (PLoc.int 1002) = Val.int 0
  )
  \/
  (
    mem (PLoc.int 1001) = Val.int 41 /\
    mem (PLoc.int 1002) = Val.int 42
  ).

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

Lemma transaction_DR:
  forall env envt,
    TypeSystem.judge env envt ->
  DR env transaction.
Proof.
  i. hexploit transaction_rw. i. des.
  eapply DR_RW; eauto.
Qed.

Theorem transaction_atomic_no_crash:
  forall p tid env tr mach_term,
    p = prog_intro env (IdMap.add tid transaction (IdMap.empty _)) ->
    Machine.rtc Machine.normal p tr (Machine.init p) mach_term ->
  consistent_state mach_term.(Machine.mem).
Proof.
  i.
  assert (INIT_CONST: consistent_state (Machine.init p).(Machine.mem)).
  { left. ss. }
  inv H0; ss. inv ONE; ss.
  { symmetry in PROG. inv PROG.
    rewrite IdMap.fold_1 in *. rewrite IdMap.add_empty in *. ss.
    rewrite IdMap.add_spec in *. des_ifs; cycle 1.
    { rewrite IdMap.gempty in THR1. ss. }
    inv THR_STEP; inv STEP; ss.
    inv STMT. inv MMT. ss. lia.
  }
  symmetry in PROG. inv PROG.
  rewrite IdMap.fold_1 in *. rewrite IdMap.add_empty in *. ss.
  rewrite IdMap.add_spec in *. des_ifs; cycle 1.
  { rewrite IdMap.gempty in THR1. ss. }
  inv e. rewrite IdMap.add_add in *.
  inv THR_STEP; inv STEP; inv STMT; inv MEM_STEP; ss; cycle 1.
  { inv EVENT. ss. }
  inv EVENT.

  inv RTC; ss. inv ONE; ss.
  { symmetry in PROG. inv PROG.
    rewrite IdMap.add_spec in *. des_ifs; cycle 1.
    { rewrite IdMap.gempty in THR1. ss. }
    inv THR_STEP; inv STEP; ss.
    inv STMT. inv MMT0. ss. lia.
  }
  symmetry in PROG. inv PROG.
  rewrite IdMap.add_spec in *. des_ifs; cycle 1.
  { rewrite IdMap.gempty in THR1. ss. }
  inv e. rewrite IdMap.add_add in *.
  inv THR_STEP; inv STEP; inv STMT; inv MEM_STEP; ss; cycle 1.
  { inv EVENT. ss. }
  inv EVENT.

  inv RTC0; ss. inv ONE; ss.
  { symmetry in PROG. inv PROG.
    rewrite IdMap.add_spec in *. des_ifs; cycle 1.
    { rewrite IdMap.gempty in THR1. ss. }
    inv THR_STEP; inv STEP; ss.
    inv STMT. inv MMT1. ss. lia.
  }
  symmetry in PROG. inv PROG.
  rewrite IdMap.add_spec in *. des_ifs; cycle 1.
  { rewrite IdMap.gempty in THR1. ss. }
  inv e. rewrite IdMap.add_add in *.
  inv THR_STEP; inv STEP; inv STMT; inv MEM_STEP; ss; cycle 1.
  { inv EVENT. ss. }
  inv EVENT.

  inv RTC; ss. inv ONE; ss.
  { symmetry in PROG. inv PROG.
    rewrite IdMap.add_spec in *. des_ifs; cycle 1.
    { rewrite IdMap.gempty in THR1. ss. }
    inv THR_STEP; inv STEP; ss.
    inv STMT. inv MMT2. ss. lia.
  }
  symmetry in PROG. inv PROG.
  rewrite IdMap.add_spec in *. des_ifs; cycle 1.
  { rewrite IdMap.gempty in THR1. ss. }
  inv e. rewrite IdMap.add_add in *.
  inv THR_STEP; inv STEP; inv STMT; inv MEM_STEP; ss; cycle 1.
  { inv EVENT. ss. }
  inv EVENT.

  inv RTC0; ss; cycle 1.
  { inv ONE; ss.
    { symmetry in PROG. inv PROG.
      rewrite IdMap.add_spec in *. des_ifs; cycle 1.
      { rewrite IdMap.gempty in THR1. ss. }
      inv THR_STEP; inv STEP; inv STMT; ss.
    }
    symmetry in PROG. inv PROG.
    rewrite IdMap.add_spec in *. des_ifs; cycle 1.
    { rewrite IdMap.gempty in THR1. ss. }
    inv THR_STEP; inv STEP; inv STMT; ss.
  }

  ii. repeat rewrite fun_add_spec in *; des_ifs; eauto.
  - exfalso. apply c2. ss.
  - exfalso. apply c1. ss.
Qed.

Theorem transaction_atomic:
  forall p tid env tr mach_term,
    p = prog_intro env (IdMap.add tid transaction (IdMap.empty _)) ->
    Machine.rtc Machine.step p tr (Machine.init p) mach_term ->
  consistent_state mach_term.(Machine.mem).
Proof.
  admit.
Qed.
