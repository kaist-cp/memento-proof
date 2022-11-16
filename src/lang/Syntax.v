Require Import ZArith.

From Memento Require Import Utils.

Set Implicit Arguments.

Create HintDb syntax discriminated.

(* TODO: paper *)
Module Val.
  Include Z.
End Val.

Definition VReg := Id.t.

(* TODO: paper *)
Inductive Expr :=
| expr_const (const: Val.t)
| expr_reg (r: VReg)
.
#[export] Hint Constructors Expr : syntax.
Coercion expr_const: Val.t >-> Expr.
Coercion expr_reg: VReg >-> Expr.

Definition Label := nat.

Inductive Stmt :=
  | stmt_assign (r: VReg) (e: Expr)
  | stmt_break
  | stmt_continue (e: Expr)
  | stmt_return (e: Expr)
  .
  #[export] Hint Constructors Stmt : syntax.

Definition FnId := Id.t.

Module Env.
  Definition t := IdMap.t (list VReg * list Stmt)%type.
End Env.

Inductive Prog :=
| prog_intro (env: Env.t) (s: list (list Stmt))
.
#[export] Hint Constructors Prog : syntax.

Module PLoc.
  Include Val.
End PLoc.
