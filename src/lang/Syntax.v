Require Import ZArith.
Require Import NArith.
Require Import EquivDec.
Require Import List.

Require Import sflib.

From Memento Require Import Utils.

Set Implicit Arguments.

Create HintDb syntax discriminated.

(* TODO: paper *)
Module Val.
  Inductive t :=
  | int (z: Z)
  | bool (b: bool)
  | tuple (tup: (t * t))
  .

  Program Instance Val_eqdec: EqDec t eq.
  Next Obligation.
  destruct x, y; try by right; ss.
  - destruct (z == z0); [left | right].
    + inv e. ss.
    + i. inv H. apply c. ss.
  - destruct (b == b0); [left | right].
    + inv e. ss.
    + i. inv H. apply c. ss.
  - admit.
  Defined.
End Val.

Definition VReg := Id.t.

(* TODO: paper *)
Inductive Expr :=
| expr_const (const: Val.t)
| expr_reg (r: VReg)
.
Hint Constructors Expr : syntax.
Coercion expr_const: Val.t >-> Expr.
Coercion expr_reg: VReg >-> Expr.

Definition Label := nat.

Definition FnId := Id.t.

Inductive Stmt :=
  | stmt_assign (r: VReg) (e: Expr)
  | stmt_pload (r: VReg) (e: Expr)
  | stmt_palloc (r: VReg) (e: Expr)
  | stmt_if (e: Expr) (s_t s_f: list Stmt)
  | stmt_loop (r: VReg) (e: Expr) (s: list Stmt)
  | stmt_continue (e: Expr)
  | stmt_break
  | stmt_call (r: VReg) (f: FnId) (e: list Expr) (lab: option Label)
  | stmt_return (e: Expr)
  | stmt_chkpt (r: VReg) (s: list Stmt) (lab: Label)
  | stmt_pcas (r: VReg) (e_loc e_old e_new: Expr) (lab: Label)
  .
  Hint Constructors Stmt : syntax.

Module Env.
  Definition t := IdMap.t (list VReg * list Stmt).
End Env.

Inductive Program :=
| prog_intro (env: Env.t) (s: IdMap.t (list Stmt))
.
Hint Constructors Program : syntax.

Module PLoc.
  Include Val.
End PLoc.
