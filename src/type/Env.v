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

  Inductive ro_judge (envt: t) (s: list Stmt) : Prop :=
  | ro_empty
    (STMT: s = [])
  | ro_assign
    r e
    (STMT: s = [stmt_assign r e])
  | ro_load
    r e
    (STMT: s = [stmt_pload r e])
  | ro_alloc
    r e
    (STMT: s = [stmt_palloc r e])
  | ro_loop
    r e s_body
    (BODY: ro_judge envt s_body)
    (STMT: s = [stmt_loop r e s_body])
  | ro_continue
    e
    (STMT: s = [stmt_continue e])
  | ro_break
    (STMT: s = [stmt_break])
  | ro_call
    r f e
    (F_TYPE: IdMap.find f envt = Some FnType.RO)
    (STMT: s = [stmt_call r f e])
  | ro_return
    e
    (STMT: s = [stmt_return e])
  | ro_seq
    s_l s_r
    (LEFT: ro_judge envt s_l)
    (RIGHT: ro_judge envt s_r)
    (STMT: s = s_l ++ s_r)
  | ro_if_then_else
    s_t s_f e
    (TRUE: ro_judge envt s_t)
    (FALSE: ro_judge envt s_f)
    (STMT: s = [stmt_if e s_t s_f])
  .

  Inductive rw_judge (envt: t) (labs: Ensemble Label) (s: list Stmt) : Prop :=
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
  | rw_chkpt
    r s_c mid lab
    (CLOS: ro_judge envt s)
    (LABS: labs = Singleton _ lab)
    (STMT: s = [stmt_chkpt r s_c (mid ++ [lab])])
    (* TODO: mid is a variable *)
  | rw_call
    r f e mid lab
    (CLOS: IdMap.find f envt = Some FnType.RW)
    (LABS: labs = Singleton _ lab)
    (STMT: s = [stmt_call r f (e ++ mid)])
    (* TODO: mid ++ lab, mid is a variable *)
  | rw_if_then_else
    labs_t labs_f e s_t s_f
    (TRUE: rw_judge envt labs_t s_t)
    (FALSE: rw_judge envt labs_f s_f)
    (LABS: labs = Union _ labs_t labs_f)
    (STMT: s = [stmt_if e s_t s_f])
  | rw_seq
    s_l s_r labs_l labs_r
    (DISJ: Disjoint _ labs_l labs_r)
    (LEFT: rw_judge envt labs_l s_l)
    (RIGHT: rw_judge envt labs_r s_r)
    (LABS: labs = Union _ labs_l labs_r)
    (STMT: s = s_l ++ s_r)
  (* TODO: Define loop simple *)
  | rw_loop
    labs' s_body r e lab mid
    (BODY: rw_judge envt labs' s_body)
    (NIN: In _ labs' lab -> False)
    (LABS: labs = Union _ (Singleton _ lab) labs')
    (STMT: s = [stmt_loop r e ((stmt_chkpt r [stmt_return r] (mid ++ [lab])) :: s_body)])
  .
End EnvType.

Module TypeSystem.
  Inductive judge (env: Env.t) (envt: EnvType.t) : Prop :=
  | env_empty
    (ENV: env = IdMap.empty _)
    (ENVT: envt = IdMap.empty _)
  | env_ro
    env0 envt0
    s prms f
    (JUDG: judge env0 envt0)
    (ROJ: EnvType.ro_judge envt s)
    (ENV: env = IdMap.add f (prms, s) env0)
    (ENVT: envt0 = IdMap.add f FnType.RO envt0)
  | env_rw
    env0 envt0
    labs s prms_all prms mid f
    (JUDG: judge env0 envt0)
    (RWJ: EnvType.rw_judge envt labs s)
    (PRMS: prms_all = prms ++ [mid])
    (ENV: env = IdMap.add f (prms_all, s) env0)
    (ENVT: envt0 = IdMap.add f FnType.RW envt0)
  .
End TypeSystem.
