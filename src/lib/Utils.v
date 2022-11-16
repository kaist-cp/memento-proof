Require Import PArith.
Require Import FMapPositive.

Axiom devil: False.
Ltac admit := exfalso; clear; case devil.

Module Id := Pos.

Module IdMap.
  Include PositiveMap.
End IdMap.
