Require Import List.
Import ListNotations.
Require Import Ensembles.

From Memento Require Import Utils.
From Memento Require Import Syntax.

Set Implicit Arguments.

Create HintDb env discriminated.

Module FnType.
  Inductive t :=
  | RO
  | RW
  .
  Hint Constructors t : env.
End FnType.

Module EnvType.
  Definition t := IdMap.t FnType.t.

  Inductive judge (envt: EnvType.t) (labs: Ensemble Label) (s: list Stmt) : Prop :=
  | rw_empty
    (LABS: labs = Empty_set _)
    (STMT: s = [])
  | rw_break
    (LABS: labs = Empty_set _)
    (STMT: s = [stmt_break])
  | rw_continue
    e
    (LABS: labs = Empty_set _)
    (STMT: s = [stmt_continue e])
  | rw_return
    e
    (LABS: labs = Empty_set _)
    (STMT: s = [stmt_return e])
  | rw_assign
    r e
    (LABS: labs = Empty_set _)
    (STMT: s = [stmt_assign r e])
  | rw_pcas
    r e_loc e_old e_new lab mid
    (LABS: labs = Singleton _ lab)
    (STMT: s = [stmt_pcas r e_loc e_old e_new (mid ++ [lab])])
    (* TODO: mid is a variable *)
  | rw_if_then_else
    labs_t labs_f e s_t s_f
    (LABS: labs = Union _ labs_t labs_f)
    (TRUE: judge envt labs_t s_t)
    (FALSE: judge envt labs_f s_f)
    (STMT: s = [stmt_if e s_t s_f])
  | rw_seq
    s_l s_r labs_l labs_r
    (DISJ: Disjoint _ labs_l labs_r)
    (LEFT: judge envt labs_l s_l)
    (RIGHT: judge envt labs_r s_r)
    (LABS: labs = Union _ labs_l labs_r)
    (STMT: s = s_l ++ s_r)
  (* TODO: Define other rules *)
  .
End EnvType.

Module TypeSystem.
  Inductive judge (env: Env.t) (envt: EnvType.t) : Prop :=
  | env_empty
    (ENV: env = IdMap.empty _)
    (ENVT: envt = IdMap.empty _)
  | env_rw
    env0 envt0
    labs s prms_all prms mid f
    (JUDG: judge env0 envt0)
    (RWJ: EnvType.judge envt labs s)
    (PRMS: prms_all = prms ++ [mid])
    (ENV: env = IdMap.add f (prms_all, s) env0)
    (ENVT: envt0 = IdMap.add f FnType.RW envt0)
  (* TODO: Define ENV-RO *)
  .
End TypeSystem.
