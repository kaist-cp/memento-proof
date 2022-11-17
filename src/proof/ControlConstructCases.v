Require Import Lia.
Require Import List.
Import ListNotations.

Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.

Set Implicit Arguments.

Lemma checkpoint_cases :
  forall env tr s s_term c c_term ts ts_term mmts mmts_term,
    (exists rmap r mid, c = [Cont.chkptcont rmap r [] mid]) ->
    Thread.rtc env tr (Thread.mk s c ts mmts) (Thread.mk s_term c_term ts_term mmts_term) [] ->
  <<CALL_ONGOING:
    exists c_pfx, c_term = c_pfx ++ c
    /\ Thread.rtc env tr (Thread.mk s [] ts mmts) (Thread.mk s_term c_pfx ts_term mmts_term) []>>
  \/
  <<CALL_DONE:
    exists s_r c_r ts_r mmts_r e,
      Thread.rtc env tr (Thread.mk s [] ts mmts) (Thread.mk ((stmt_return e) :: s_r) c_r ts_r mmts_r) []
      /\ Thread.step env [] (Thread.mk ((stmt_return e) :: s_r) (c_r ++ c) ts_r mmts_r) (Thread.mk s_term c_term ts_term mmts_term)
      /\ s_term = [] /\ c_term = []>>.
Proof.
  admit.
Qed.
