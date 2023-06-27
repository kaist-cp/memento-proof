Require Import PArith.
Require Import ZArith.
Require Import List.
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
Definition prog := [
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

Lemma prog_rw:
  forall envt,
    exists labs, EnvType.rw_judge envt labs prog.
Proof.
  i. unfold prog. esplits.
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

Lemma prog_DR:
  forall env envt,
    TypeSystem.judge env envt ->
  DR env prog.
Proof.
  i. hexploit prog_rw. i. des.
  eapply DR_RW; eauto.
  admit. (* DR trivial lemma *)
Qed.

