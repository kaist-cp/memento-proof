Require Import ZArith.

From Memento Require Import Utils.

Module Val.
  Include Z.

  Definition default: t := 0.
End Val.

Module Loc.
  Include Val.
End Loc.

Definition FuncId := Id.t.

Definition Env := 1.

(* Inductive Prog :=
| prog_intro (e: Env)
.
Hint Constructors Prog. *)
