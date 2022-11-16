Require Import List.
Import ListNotations.
Require Import Relations.

From Memento Require Import Syntax.
From Memento Require Import Semantics.

Set Implicit Arguments.

Definition STOP (s: list Stmt) (c: list Cont.t) :=
  (s = [] /\ c = [])
  \/ (exists s_rem, s = stmt_break :: s_rem /\ c = [])
  \/ (exists s_rem e, s = (stmt_continue e) :: s_rem /\ c = [])
  \/ (exists s_rem e, s = (stmt_return e) :: s_rem /\ (Cont.Loops c))
  .

Inductive trace_refine (tr1 tr2: list Event.t) : Prop :=
| refine_empty
  (EMPTY: trace_refine [] [])
| refine_both
  ev
  (REFINE: trace_refine tr1 tr2)
  (BOTH: trace_refine (tr1 ++ [ev]) (tr2 ++ [ev]))
| refine_read
  l v
  (REFINE: trace_refine tr1 tr2)
  (BOTH: trace_refine tr1 (tr2 ++ [Event.R l v]))
.

Notation "tr1 ~ tr2" := (trace_refine tr1 tr2) (at level 62).

Definition DR (env: Env.t) (s: list Stmt) :=
  forall tr tr' thr thr' thr_term thr_term' ts mmts,
    thr = Thread.mk s [] ts mmts ->
    thr' = Thread.mk s [] ts thr_term.(Thread.mmts) ->
    Thread.rtc env tr thr thr_term [] ->
    Thread.rtc env tr' thr' thr_term' [] ->
  exists tr_x s_x c_x ts_x,
    Thread.rtc env tr_x thr (Thread.mk s_x c_x ts_x thr_term'.(Thread.mmts)) []
    /\ tr_x ~ tr ++ tr'
    /\ (STOP thr_term.(Thread.stmt) thr_term.(Thread.cont) ->
          thr_term.(Thread.stmt) = s_x
          /\ thr_term.(Thread.cont) = c_x
          /\ thr_term.(Thread.ts) = ts_x
          /\ thr_term.(Thread.mmts) = thr_term'.(Thread.mmts)
          /\ [] ~ tr')
    /\ (STOP thr_term'.(Thread.stmt) thr_term'.(Thread.cont) ->
          thr_term'.(Thread.stmt) = s_x
          /\ thr_term'.(Thread.cont) = c_x
          /\ thr_term'.(Thread.ts) = ts_x)
  .
