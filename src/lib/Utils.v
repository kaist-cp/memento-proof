Require Import PArith.

Axiom devil: False.
Ltac admit := exfalso; clear; case devil.

Module Id := Pos.
