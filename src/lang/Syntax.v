Require Import ZArith.
Require Import NArith.
Require Import EquivDec.
Require Import List.
Import ListNotations.

Require Import sflib.

From Memento Require Import Utils.

Set Implicit Arguments.

(* Figure 16 *)
Definition Label := nat.

Definition VReg := nat.

Definition mid : VReg := 0.

Definition FnId := Id.t.

Definition PLoc := N.

Instance N_eqdec: EqDec N eq := N.eq_dec.

Module Val.
  Inductive t :=
  | unit
  | int (z: Z)
  | bool (b: bool)
  | mid (m: list Label)
  | pair (v1 v2: t)
  | inl (v: t)
  | inr (v: t)
  .

  Definition eq_dec: forall (x y: t), {x = y} + {x <> y}.
  Proof.
    decide equality; first [apply Z.eq_dec | apply Bool.bool_dec | apply (list_eq_dec Nat.eq_dec)].
  Defined.

  Instance eqdec: EqDec t eq := eq_dec.
End Val.

Inductive Op :=
| op_add
| op_sub
| op_mul
| op_eq
| op_lt
| op_and
| op_or
.

Inductive Expr :=
| expr_unit
| expr_int (z: Z)
| expr_bool (b: bool)
| expr_reg (r: VReg)
| expr_op (op: Op) (e1 e2: Expr)
| expr_proj (e: Expr) (i: bool)
| expr_pair (e1 e2: Expr)
| expr_inl (e: Expr)
| expr_inr (e: Expr)
| expr_match (e: Expr) (xl: VReg) (el: Expr) (xr: VReg) (er: Expr)
| expr_eps
| expr_lab (e: Expr) (lab: Label)
.

Definition expr_mid (lab: Label) : Expr := expr_lab (expr_reg mid) lab.

Fixpoint free_in (x: VReg) (e: Expr) : Prop :=
  match e with
  | expr_reg r => x = r
  | expr_op _ e1 e2 | expr_pair e1 e2 => free_in x e1 \/ free_in x e2
  | expr_proj e _ | expr_inl e | expr_inr e | expr_lab e _ => free_in x e
  | expr_match e xl el xr er => free_in x e \/ (x <> xl /\ free_in x el) \/ (x <> xr /\ free_in x er)
  | _ => False
  end.

Definition midfree (e: Expr) : Prop := ~ free_in mid e.

Inductive Stmt :=
| stmt_assign (r: VReg) (e: Expr)
| stmt_pload (r: VReg) (e: Expr)
| stmt_palloc (r: VReg) (e: Expr)
| stmt_if (e: Expr) (s_t s_f: list Stmt)
| stmt_loop (r: option VReg) (e: Expr) (s: list Stmt)
| stmt_continue (e: Expr)
| stmt_break
| stmt_call (r: VReg) (f: FnId) (es: list Expr)
| stmt_return (e: Expr)
| stmt_chkpt (r: VReg) (s: list Stmt) (e_mid: Expr)
| stmt_pcas (r: VReg) (e_loc e_old e_new e_mid: Expr)
.

Fixpoint midfree_stmt (x: Stmt) : Prop :=
  match x with
  | stmt_assign _ e | stmt_pload _ e | stmt_palloc _ e | stmt_continue e | stmt_return e => midfree e
  | stmt_if e s_t s_f =>
      midfree e
      /\ fold_right (fun y P => midfree_stmt y /\ P) True s_t
      /\ fold_right (fun y P => midfree_stmt y /\ P) True s_f
  | stmt_loop _ e s => midfree e /\ fold_right (fun y P => midfree_stmt y /\ P) True s
  | stmt_break => True
  | stmt_call _ _ es => Forall midfree es
  | stmt_chkpt _ s e => fold_right (fun y P => midfree_stmt y /\ P) True s /\ midfree e
  | stmt_pcas _ el eo en em => midfree el /\ midfree eo /\ midfree en /\ midfree em
  end.

Definition midfree_stmts (s: list Stmt) : Prop := fold_right (fun y P => midfree_stmt y /\ P) True s.

Module Env.
  Definition t := IdMap.t (list VReg * list Stmt).
End Env.

Record Program := mk_program {
  prog_env: Env.t;
  prog_threads: list (list Stmt);
}.
