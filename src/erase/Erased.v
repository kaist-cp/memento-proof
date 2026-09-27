Require Import ZArith.
Require Import NArith.
Require Import EquivDec.
Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.

Set Implicit Arguments.

Inductive EStmt :=
| estmt_assign (r: VReg) (e: Expr)
| estmt_pload (r: VReg) (e: Expr)
| estmt_palloc (r: VReg) (e: Expr)
| estmt_if (e: Expr) (s_t s_f: list EStmt)
| estmt_loop (r: option VReg) (e: Expr) (s: list EStmt)
| estmt_continue (e: Expr)
| estmt_break
| estmt_call (r: VReg) (f: FnId) (es: list Expr)
| estmt_return (e: Expr)
| estmt_blk (r: VReg) (s: list EStmt)
| estmt_cas (r: VReg) (e_loc e_old e_new: Expr)
.

Module EEnv.
  Definition t := IdMap.t (list VReg * list EStmt).
End EEnv.

Record EProgram := mk_eprogram {
  eprog_env: EEnv.t;
  eprog_threads: list (list EStmt);
}.

Module ECont.
  Inductive t :=
  | loopcont (rmap: VRegMap.t) (r: option VReg) (s_body: list EStmt) (s_cont: list EStmt)
  | fncont (rmap: VRegMap.t) (r: VReg) (s_cont: list EStmt)
  | blkcont (rmap: VRegMap.t) (r: VReg) (s_cont: list EStmt)
  .

  Definition is_loop (c: t) :=
    match c with
    | loopcont _ _ _ _ => true
    | _ => false
    end.

  Definition Loops (c: list t) := Forall is_loop c.
End ECont.

Module EThread.
  Record t := mk {
    stmt: list EStmt;
    cont: list ECont.t;
    regs: VRegMap.t;
  }.

  Inductive step (env: EEnv.t) : list Event.t -> t -> t -> Prop :=
  | step_assign
      r e s c regs v
      (EVAL: sem_expr regs e = Some v)
    : step env [] (mk (estmt_assign r e :: s) c regs) (mk s c (VRegMap.add r v regs))
  | step_pload
      r e s c regs vl l v
      (EVAL: sem_expr regs e = Some vl)
      (LOC: as_loc vl = Some l)
    : step env [Event.R l v] (mk (estmt_pload r e :: s) c regs) (mk s c (VRegMap.add r v regs))
  | step_palloc
      r e s c regs v l
      (EVAL: sem_expr regs e = Some v)
    : step env [Event.R l v] (mk (estmt_palloc r e :: s) c regs)
        (mk s c (VRegMap.add r (Val.int (Z.of_N l)) regs))
  | step_branch
      e s_t s_f s c regs b
      (EVAL: sem_expr regs e = Some (Val.bool b))
    : step env [] (mk (estmt_if e s_t s_f :: s) c regs) (mk ((if b then s_t else s_f) ++ s) c regs)
  | step_loop
      r e s_body s c regs v
      (EVAL: sem_expr regs e = Some v)
    : step env [] (mk (estmt_loop r e s_body :: s) c regs)
        (mk s_body (ECont.loopcont regs r s_body s :: c) (set_opt r v regs))
  | step_continue
      e s c regs v rmap r s_body s_cont c'
      (EVAL: sem_expr regs e = Some v)
      (CONT: c = ECont.loopcont rmap r s_body s_cont :: c')
    : step env [] (mk (estmt_continue e :: s) c regs) (mk s_body c (set_opt r v rmap))
  | step_break
      s c regs rmap r s_body s_cont c'
      (CONT: c = ECont.loopcont rmap r s_body s_cont :: c')
    : step env [] (mk (estmt_break :: s) c regs) (mk s_cont c' rmap)
  | step_call
      r f es s c regs vs prms s_f
      (EVAL: sem_exprs regs es = Some vs)
      (FIND: IdMap.find f env = Some (prms, s_f))
      (ARITY: length prms = length vs)
    : step env [] (mk (estmt_call r f es :: s) c regs)
        (mk s_f (ECont.fncont regs r s :: c) (bind_params prms vs))
  | step_return
      e s c regs v c_loops rmap r s2 c2
      (EVAL: sem_expr regs e = Some v)
      (CONT: c = c_loops ++ ECont.fncont rmap r s2 :: c2)
      (LOOPS: ECont.Loops c_loops)
    : step env [] (mk (estmt_return e :: s) c regs) (mk s2 c2 (VRegMap.add r v rmap))
  | step_blk_call
      r s_b s c regs
    : step env [] (mk (estmt_blk r s_b :: s) c regs) (mk s_b (ECont.blkcont regs r s :: c) regs)
  | step_blk_return
      e s c regs v c_loops rmap r s2 c2
      (EVAL: sem_expr regs e = Some v)
      (CONT: c = c_loops ++ ECont.blkcont rmap r s2 :: c2)
      (LOOPS: ECont.Loops c_loops)
    : step env [] (mk (estmt_return e :: s) c regs) (mk s2 c2 (VRegMap.add r v rmap))
  | step_cas_succ
      r e_loc e_old e_new s c regs vl l v_old v_new
      (LOC: sem_expr regs e_loc = Some vl)
      (AS_LOC: as_loc vl = Some l)
      (OLD: sem_expr regs e_old = Some v_old)
      (NEW: sem_expr regs e_new = Some v_new)
    : step env [Event.U l v_old v_new] (mk (estmt_cas r e_loc e_old e_new :: s) c regs)
        (mk s c (VRegMap.add r (Val.pair (Val.bool true) v_old) regs))
  | step_cas_fail
      r e_loc e_old e_new s c regs vl l v_old v
      (LOC: sem_expr regs e_loc = Some vl)
      (AS_LOC: as_loc vl = Some l)
      (OLD: sem_expr regs e_old = Some v_old)
      (NE: v <> v_old)
    : step env [Event.R l v] (mk (estmt_cas r e_loc e_old e_new :: s) c regs)
        (mk s c (VRegMap.add r (Val.pair (Val.bool false) v) regs))
  .
End EThread.

Module EMachine.
  Record t := mk {
    tmap: IdMap.t EThread.t;
    mem: Mem.t;
  }.

  Definition init_thread (s: list EStmt) : EThread.t := EThread.mk s [] VRegMap.empty.

  Definition init (q: EProgram) : t :=
    mk (IdMap.map init_thread (tmap_of 1 q.(eprog_threads))) Mem.init.

  Inductive normal (q: EProgram) (tr: list Event.t) (mach1 mach2: t) : Prop :=
  | normal_intro
      tid thr1 thr2 tr_t mem2
      (THR1: IdMap.find tid mach1.(tmap) = Some thr1)
      (THR_STEP: EThread.step q.(eprog_env) tr_t thr1 thr2)
      (MEM_STEP: Mem.rtc tr_t mach1.(mem) mem2)
      (TRACE: tr = filter_updates tr_t)
      (MACHINE2: mach2 = mk (IdMap.add tid thr2 mach1.(tmap)) mem2)
  .

  Inductive rtc (q: EProgram) : list Event.t -> t -> t -> Prop :=
  | rtc_refl
      mach
    : rtc q [] mach mach
  | rtc_tc
      tr tr0 tr1 mach mach0 mach_term
      (ONE: normal q tr0 mach mach0)
      (RTC: rtc q tr1 mach0 mach_term)
      (TRACE: tr = tr0 ++ tr1)
    : rtc q tr mach mach_term
  .
End EMachine.

Definition EB (q: EProgram) : Ensemble (list Event.t) :=
  fun tr => exists mach, EMachine.rtc q tr (EMachine.init q) mach.
