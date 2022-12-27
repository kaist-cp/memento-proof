Require Import Ensembles.
Require Import EquivDec.
Require Import List.
Import ListNotations.

Require Import HahnList.
Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Common.
From Memento Require Import Env.

Set Implicit Arguments.

Lemma lift_cont:
  forall env tr thr thr_term c,
    Thread.rtc env [] tr thr thr_term ->
  Thread.rtc env c tr
    (Thread.mk thr.(Thread.stmt) (thr.(Thread.cont) ++ c) thr.(Thread.ts) thr.(Thread.mmts))
    (Thread.mk thr_term.(Thread.stmt) (thr_term.(Thread.cont) ++ c) thr_term.(Thread.ts) thr_term.(Thread.mmts)).
Proof.
  i. induction H; subst.
  { econs; eauto. }
  econs 2; eauto. econs; ss.
  inv ONE. rewrite app_nil_r in *. subst. inv NORMAL_STEP; inv STEP; ss.
  - econs. econs; eauto.
  - econs 2. econs; eauto.
  - econs 3. econs; eauto.
  - econs 4. econs; eauto.
  - econs 5. econs; eauto.
  - econs 6. econs; eauto.
  - econs 7. econs; eauto.
  - econs 8. econs; eauto.
    ss. rewrite CONT. rewrite <- app_assoc. ss.
  - econs 9. econs; eauto.
  - econs 10. econs; eauto.
  - econs 11. econs; eauto.
  - econs 12. econs; eauto.
    ss. rewrite CONT. ss.
  - econs 13. econs; eauto.
    ss. rewrite CONT. ss.
  - econs 14. econs; eauto.
  - econs 15. econs; eauto.
    ss. rewrite CONT. rewrite <- app_assoc. ss.
Qed.

Lemma chkpt_fn_cases:
  forall env tr thr thr_term c c' rmap r s_cont,
    Thread.rtc env [] tr thr thr_term ->
    thr.(Thread.cont) = c ++ [c'] ->
    ((exists mid, c' = Cont.chkptcont rmap r s_cont mid) \/ c' = Cont.fncont rmap r s_cont) ->
  <<CALL_ONGOING:
    exists c_pfx,
      thr_term.(Thread.cont) = c_pfx ++ [c']
      /\ Thread.rtc env [] tr
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts))
      /\ Thread.rtc env [c'] tr thr thr_term>>
  \/
  <<CALL_DONE:
    exists tr0 tr1 s_r c_r ts_r mmts_r e,
      tr = tr0 ++ tr1
      /\ Thread.rtc env [] tr0
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk ((stmt_return e) :: s_r) c_r ts_r mmts_r)
      /\ Thread.rtc env [c'] tr0
          thr
          (Thread.mk ((stmt_return e) :: s_r) (c_r ++ [c']) ts_r mmts_r)
      /\ Thread.tc env [] tr1 (Thread.mk ((stmt_return e) :: s_r) (c_r ++ [c']) ts_r mmts_r) thr_term
      /\ Cont.Loops c_r>>.
Proof.
  intros env tr thr thr_term c c' rmap r s_cont RTC. revert rmap r c c' s_cont.
  induction RTC; i; subst.
  { left. esplits; eauto; econs; ss. }
  guardH H0.
  inversion ONE. rewrite app_nil_r in *. subst. inv NORMAL_STEP; inv STEP; ss.
  - hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs. econs; eauto.
    + right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
    + right. subst. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 2.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
    + right. subst. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 2.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
    + right. subst. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 2.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 5. econs; eauto.
    + right. subst. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 2.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
    + right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := _ :: _). ss. }
    i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
    + right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
      { subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 7. econs; eauto. ss.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [c']).
    { clear - c2 CONT.
      destruct c2 using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. des; ss. inv H0.
      inv ONE.
      right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; try by econs; eauto.
      { rewrite app_nil_l. ss. }
      econs; eauto. econs; eauto.
    + hexploit IHRTC; eauto. i. des.
      * left. eexists. seqsplit; eauto; cycle 1.
        { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 8. econs; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
      * right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
        { subst. hexploit lift_cont; eauto. }
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 8. econs; try exact LOOPS; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
    + right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
    + right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
      { destruct thr, thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := _ :: _). ss. }
    i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
    + right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
      { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - destruct thr. ss. subst.
    assert (c_rem = [] \/ exists c_rem', c_rem = c_rem' ++ [c']).
    { clear - c_rem CONT.
      destruct c_rem using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    { unguard. rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des; subst; ss. }
    hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 12. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
    + right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
      { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 12. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [c']).
    { clear - c2 CONT.
      destruct c2 using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. ss. inv CONT.
      esplits. eauto.
    }
    des; subst.
    { unguard. rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des; subst; ss. }
    hexploit IHRTC; eauto. i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
    + right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
      { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := _ :: _). ss. }
    i. des.
    + left. eexists. seqsplit; eauto; cycle 1.
      { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
    + right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
      { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [c']).
    { clear - c2 CONT.
      destruct c2 using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + right.
      rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. des; ss. inv H0.
      inv ONE.
      eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; try by econs; eauto.
      { rewrite app_nil_l. ss. }
      econs; eauto. econs; eauto.
    + hexploit IHRTC; eauto. i. des.
      * left. eexists. seqsplit; eauto; cycle 1.
        { destruct thr_term. ss. subst. hexploit lift_cont; eauto. }
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 15. econs; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
      * right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; cycle 1.
        { subst. hexploit lift_cont; eauto. }
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 15. econs; try exact LOOPS; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
Qed.

Lemma loop_cases:
  forall env tr thr thr_term c c' rmap r s_body s_cont,
    Thread.rtc env [] tr thr thr_term ->
    thr.(Thread.cont) = c ++ [c'] ->
    c' = Cont.loopcont rmap r s_body s_cont ->
  <<LOOP_ONGOING: Thread.rtc env [c'] tr thr thr_term>>
  \/
  <<LOOP_DONE:
      exists tr0 tr1 s_r ts_r mmts_r,
        tr = tr0 ++ tr1
        /\ Thread.rtc env [c'] tr0
            thr
            (Thread.mk (stmt_break :: s_r) [c'] ts_r mmts_r)
        /\ Thread.rtc env [] tr1
            (Thread.mk s_cont [] (TState.mk rmap ts_r.(TState.time)) mmts_r)
            thr_term>>.
Proof.
  intros env tr thr thr_term c c' rmap r s_body s_cont RTC. revert rmap r s_body s_cont c c'.
  induction RTC; i.
  { left. econs; ss. }
  guardH H0. subst.
  inversion ONE. rewrite app_nil_r in *. subst. inv NORMAL_STEP; inv STEP; ss.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 2. econs; eauto.
    + right. subst. esplits; eauto.
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 2. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 3. econs; eauto.
    + right. subst. esplits; eauto.
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 3. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 4. econs; eauto.
    + right. subst. esplits; eauto.
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 4. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 5. econs; eauto.
    + right. subst. esplits; eauto.
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 5. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs 6. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs 6. econs; eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss.
      { econs 7. econs; eauto. ss. }
      instantiate (1 := _ :: _). ss.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss.
      { econs 7. econs; eauto. ss. }
      instantiate (1 := _ :: _). ss.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [c']).
    { clear - c2 CONT.
      destruct c2 using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + right.
      rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. ss.
    + hexploit IHRTC; eauto. i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss. econs 8. econs; eauto; ss.
      * right. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss. econs 8. econs; eauto; ss.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs 9. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs 9. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs 10. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs 10. econs; eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss. econs 11. econs; eauto; ss.
      instantiate (1 := _ :: _). ss.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss. econs 11. econs; eauto; ss.
      instantiate (1 := _ :: _). ss.
  - destruct thr. ss. subst.
    assert (c_rem = [] \/ exists c_rem', c_rem = c_rem' ++ [c']).
    { clear - c_rem CONT.
      destruct c_rem using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. des; ss. inv H0.
      hexploit IHRTC; eauto.
      { rewrite app_nil_l. ss. }
      i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_l]; ss. econs 12. econs; eauto; ss.
      * right. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_l]; ss. econs 12. econs; eauto; ss.
    + hexploit IHRTC; eauto. i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss. econs 12. econs; eauto; ss.
      * right. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss. econs 12. econs; eauto; ss.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [c']).
    { clear - c2 CONT.
      destruct c2 using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. inv H0. rewrite app_nil_l in *.
      right. esplits; eauto; [rewrite app_nil_l |]; ss.
      econs; eauto.
    + hexploit IHRTC; eauto. i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss. econs 13. econs; eauto; ss.
      * right. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss. econs 13. econs; eauto; ss.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss. econs 14. econs; eauto; ss.
      instantiate (1 := _ :: _). ss.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss. econs 14. econs; eauto; ss.
      instantiate (1 := _ :: _). ss.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [c']).
    { clear - c2 CONT.
      destruct c2 using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + right.
      rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. ss.
    + hexploit IHRTC; eauto. i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss. econs 15. econs; eauto; ss.
      * right. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss. econs 15. econs; eauto; ss.
Qed.

Lemma first_loop_iter:
  forall env tr thr thr_term c c' rmap r s,
    Thread.rtc env [c'] tr thr thr_term ->
    thr.(Thread.cont) = c ++ [c'] ->
    c' = Cont.loopcont rmap r s [] ->
  <<FIRST_ONGOING:
      exists c_pfx, thr_term.(Thread.cont) = c_pfx ++ [c']
        /\ Thread.rtc env [] tr
            (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
            (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts))>>
  \/
  <<FIRST_DONE:
    exists tr1 tr2 e s1 ts1 mmts1,
      tr = tr1 ++ tr2
      /\ Thread.rtc env [] tr1
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk ((stmt_continue e) :: s1) [] ts1 mmts1)
      /\ Thread.rtc env [c'] tr2
          (Thread.mk ((stmt_continue e) :: s1) [c'] ts1 mmts1)
          thr_term>>.
Proof.
  intros env tr thr thr_term c c' rmap r s RTC. revert rmap r s c.
  induction RTC; i; subst.
  { left. esplits; eauto. econs; ss. }
  inversion ONE. inv NORMAL_STEP; inv STEP; destruct thr; ss; subst.
  - apply app_inv_tail in BASE. subst.
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs. econs; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs. econs; ss.
  - apply app_inv_tail in BASE. subst.
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; ss; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 2. econs; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; ss; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 2. econs; ss.
  - apply app_inv_tail in BASE. subst.
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; ss; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 3. econs; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; ss; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 3. econs; ss.
  - apply app_inv_tail in BASE. subst.
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; ss; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 4. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; ss; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 4. econs; eauto; ss.
  - apply app_inv_tail in BASE. subst.
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; ss; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 5. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      { instantiate (1 := _ :: _). ss. }
      econs 2; eauto; ss; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 5. econs; eauto; ss.
  - apply app_inv_tail in BASE. subst.
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 6. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 6. econs; eauto; ss.
  - rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst.
    hexploit IHRTC; try rewrite app_comm_cons; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 7. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 7. econs; eauto; ss.
  - rewrite app_comm_cons in CONT. rewrite app_assoc in CONT. apply app_inv_tail in CONT. subst.
    hexploit IHRTC; try rewrite app_comm_cons; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 8. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 8. econs; eauto; ss.
  - apply app_inv_tail in BASE. subst.
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 9. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 9. econs; eauto; ss.
  - apply app_inv_tail in BASE. subst.
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 10. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 10. econs; eauto; ss.
  - rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst.
    hexploit IHRTC; try rewrite app_comm_cons; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 11. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 11. econs; eauto; ss.
  - apply app_inv_tail in BASE. subst.
    destruct c' as [| t c']; ss.
    + subst. right. esplits; try by econs; eauto.
      repeat rewrite app_nil_l. ss.
    + destruct t; ss. inv CONT.
      hexploit IHRTC; try rewrite app_comm_cons; eauto. i. des.
      * left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; eauto; [| rewrite app_nil_r]; ss.
        try by econs; econs; eauto.
      * right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; eauto; [| rewrite app_nil_r]; ss.
        try by econs; econs; eauto.
  - rewrite app_comm_cons in CONT. apply app_inv_tail in CONT. subst.
    hexploit IHRTC; try rewrite app_comm_cons; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss.
  - rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst.
    hexploit IHRTC; try rewrite app_comm_cons; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 14. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 14. econs; eauto; ss.
  - rewrite app_comm_cons in CONT. rewrite app_assoc in CONT. apply app_inv_tail in CONT. subst.
    hexploit IHRTC; try rewrite app_comm_cons; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 15. econs; eauto; ss.
    + rewrite FIRST_DONE. right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 15. econs; eauto; ss.
Qed.

Lemma last_loop_iter:
  forall env tr thr thr_term c_pfx c' rmap r s,
    Thread.rtc env [c'] tr thr thr_term ->
    thr.(Thread.cont) = c_pfx ++ [c'] ->
    c' = Cont.loopcont rmap r s [] ->
  exists tr1 tr2 s1 c1 ts1 mmts1 c_pfx_term,
    tr = tr1 ++ tr2
    /\ __guard__(
        <<LAST_FIRST:
          s1 = thr.(Thread.stmt)
          /\ c1 = c_pfx
          /\ ts1 = thr.(Thread.ts) /\ mmts1 = thr.(Thread.mmts)
          /\ tr1 = []>>
        \/
        <<LAST_CONT:
          exists e s_r ts_r,
            Thread.rtc env [c'] tr1
              thr
              (Thread.mk ((stmt_continue e) :: s_r) [c'] ts_r mmts1)
            /\ s1 = s
            /\ c1 = []
            /\ ts1 = TState.mk (VRegMap.add r (sem_expr ts_r.(TState.regs) e) rmap) ts_r.(TState.time)>>
      )
    /\ thr_term.(Thread.cont) = c_pfx_term ++ [c']
    /\ Thread.rtc env [] tr2
          (Thread.mk s1 c1 ts1 mmts1)
          (Thread.mk thr_term.(Thread.stmt) c_pfx_term thr_term.(Thread.ts) thr_term.(Thread.mmts)).
Proof.
  intros env tr thr thr_term c_pfx c' rmap r s RTC. revert rmap r s c_pfx.
  induction RTC; i; subst.
  { esplits; eauto; try by econs; eauto. rewrite app_nil_r. ss. }
  inversion ONE. inv NORMAL_STEP; inv STEP; destruct thr; ss; subst.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs. econs; ss.
      apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 2. econs; eauto; ss.
      apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto.
      { instantiate (1 := _ :: _). ss. }
      esplits; eauto. econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 3. econs; eauto; ss.
      apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto.
      { instantiate (1 := _ :: _). ss. }
      esplits; eauto. econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 4. econs; eauto; ss.
      apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto.
      { instantiate (1 := _ :: _). ss. }
      esplits; eauto. econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 5. econs; eauto; ss.
      apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto.
      { instantiate (1 := _ :: _). ss. }
      esplits; eauto. econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 6. econs; eauto; ss.
      apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 7. econs; eauto; ss.
      rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 8. econs; eauto; ss.
      rewrite app_comm_cons in CONT. rewrite app_assoc in CONT. apply app_inv_tail in CONT. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 9. econs; eauto; ss.
      apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 10. econs; eauto; ss.
      apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 11. econs; eauto; ss.
      rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
  - apply app_inv_tail in BASE. subst. ss.
    hexploit IHRTC; eauto. i. des.
    destruct c' as [| t c']; ss.
    + inv CONT. esplits; eauto.
      right. unguard. des; subst; ss; esplits; eauto; econs; eauto.
    + destruct t; ss. inv CONT.
      unguard. des; subst; ss.
      * esplits; [| left | |]; ss; eauto.
        { rewrite app_nil_l. ss. }
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 12. econs; eauto; ss.
      * esplits; eauto. right. esplits; eauto.
        econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss.
      rewrite app_comm_cons in CONT. apply app_inv_tail in CONT. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 14. econs; eauto; ss.
      rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
  - hexploit IHRTC; eauto. i. unguard. des; subst; ss.
    + esplits; [| left | |]; ss; eauto.
      { rewrite app_nil_l. ss. }
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 15. econs; eauto; ss.
      rewrite app_comm_cons in CONT. rewrite app_assoc in CONT. apply app_inv_tail in CONT. subst. ss.
    + esplits; [| right | |]; ss; eauto. esplits; eauto.
      econs 2; eauto.
Qed.

Lemma ongoing_cont_explosion:
  forall env tr thr thr_term c c'
         rmap r s_cont
         c0 s_cont0 c_pfx,
    Thread.rtc env [c'] tr thr thr_term ->
    thr.(Thread.cont) = c ++ [c'] ->
    thr_term.(Thread.cont) = c_pfx ++ [c'] ->
    ((exists s_body,
        c' = Cont.loopcont rmap r s_body s_cont
        /\ c0 = Cont.loopcont rmap r s_body s_cont0)
     \/
     (exists mid,
        c' = Cont.chkptcont rmap r s_cont mid
        /\ c0 = Cont.chkptcont rmap r s_cont0 mid)
     \/
     (c' = Cont.fncont rmap r s_cont
      /\ c0 = Cont.fncont rmap r s_cont0)
    ) ->
  Thread.rtc env [c0] tr
    (Thread.mk thr.(Thread.stmt) (c ++ [c0]) thr.(Thread.ts) thr.(Thread.mmts))
    (Thread.mk thr_term.(Thread.stmt) (c_pfx ++ [c0]) thr_term.(Thread.ts) thr_term.(Thread.mmts)).
Proof.
  intros env tr thr thr_term c c' rmap r s_cont c0 s_cont0 c_pfx RTC.
  revert c rmap r s_cont c0 s_cont0 c_pfx.
  induction RTC; i; subst.
  { rewrite H in H0. apply app_inv_tail in H0. subst. econs. }
  inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - rewrite H in BASE. apply app_inv_tail in BASE. subst.
    econs; eauto; cycle 1.
    { rewrite app_nil_l. ss. }
     econs; ss. try by econs; econs; eauto.
  - rewrite H in BASE. apply app_inv_tail in BASE. subst.
    econs; eauto; cycle 1.
    { instantiate (1 := [_]). ss. }
     econs; ss. try by econs; econs; eauto.
  - rewrite H in BASE. apply app_inv_tail in BASE. subst.
    econs; eauto; cycle 1.
    { instantiate (1 := [_]). ss. }
     econs; ss. try by econs; econs; eauto.
  - rewrite H in BASE. apply app_inv_tail in BASE. subst.
    econs; eauto; cycle 1.
    { instantiate (1 := [_]). ss. }
     econs; ss. try by econs; econs; eauto.
  - rewrite H in BASE. apply app_inv_tail in BASE. subst.
    econs; eauto; cycle 1.
    { instantiate (1 := [_]). ss. }
     econs; ss. try by econs; econs; eauto.
  - rewrite H in BASE. apply app_inv_tail in BASE. subst.
    econs; eauto; cycle 1.
    { rewrite app_nil_l. ss. }
    econs; ss. try by econs; econs; eauto.
  - rewrite H in BASE. rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst.
    rewrite STMT. econs; cycle 2.
    { rewrite app_nil_l. ss. }
    { econs; try by econs; econs; eauto. ss. instantiate (1 := _ :: _). ss. }
    ss. hexploit IHRTC; eauto.
    { rewrite H. instantiate (1 := _ :: _). ss. }
    i. eauto.
  - rewrite H in CONT. rewrite BASE in CONT. rewrite app_comm_cons in CONT. rewrite app_assoc in CONT. apply app_inv_tail in CONT. subst.
    econs; eauto; cycle 1.
    { rewrite app_nil_l. ss. }
    econs; ss. rewrite STMT. econs 8. econs; eauto; ss.
    rewrite <- app_assoc. ss.
  - rewrite H in BASE. apply app_inv_tail in BASE. subst.
    econs; eauto; cycle 1.
    { rewrite app_nil_l. ss. }
    econs; ss. try by econs; econs; eauto.
  - rewrite H in BASE. apply app_inv_tail in BASE. subst.
    econs; eauto; cycle 1.
    { rewrite app_nil_l. ss. }
    econs; ss. try by econs; econs; eauto.
  - rewrite H in BASE. rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst.
    rewrite STMT. econs; cycle 2.
    { rewrite app_nil_l. ss. }
    { econs; try by econs; econs; eauto. ss. instantiate (1 := _ :: _). ss. }
    ss. hexploit IHRTC; eauto.
    { rewrite H. instantiate (1 := _ :: _). ss. }
    i. eauto.
  - rewrite H in BASE. apply app_inv_tail in BASE. subst.
    rewrite H in CONT. destruct c'0; ss.
    + inv CONT. des; ss. inv H1.
      rewrite STMT. econs; cycle 2.
      { rewrite app_nil_l. ss. }
      { econs; try by econs; econs; eauto. ss. rewrite app_nil_l. ss. }
      ss. hexploit IHRTC; eauto.
      { rewrite H. rewrite app_nil_l. ss. }
      i. ss. eauto.
    + inv CONT.
      rewrite STMT. econs; cycle 2.
      { rewrite app_nil_l. ss. }
      { econs; try by econs; econs; eauto. ss. instantiate (1 := _ :: _). ss. }
      ss. hexploit IHRTC; eauto.
      { rewrite H. instantiate (1 := _ :: _). ss. }
      i. ss.
  - rewrite H in CONT. rewrite BASE in CONT. rewrite app_comm_cons in CONT. apply app_inv_tail in CONT. subst.
    econs; eauto; cycle 1.
    { rewrite app_nil_l. ss. }
    econs; ss. try by econs; econs; eauto.
  - rewrite H in BASE. rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst.
    rewrite STMT. econs; cycle 2.
    { rewrite app_nil_l. ss. }
    { econs; try by econs; econs; eauto. ss. instantiate (1 := _ :: _). ss. }
    ss. hexploit IHRTC; eauto.
    { rewrite H. instantiate (1 := _ :: _). ss. }
    i. eauto.
  - rewrite H in CONT. rewrite BASE in CONT. rewrite app_comm_cons in CONT. rewrite app_assoc in CONT. apply app_inv_tail in CONT. subst.
    econs; eauto; cycle 1.
    { rewrite app_nil_l. ss. }
    econs; ss. rewrite STMT. econs 15. econs; eauto; ss.
    rewrite <- app_assoc. ss.
Qed.

Lemma relax_base_cont:
  forall env tr thr thr_term c_base c_pfx c_sfx,
    Thread.step_base_cont env c_base tr thr thr_term ->
    c_base = c_pfx ++ c_sfx ->
  Thread.step_base_cont env c_sfx tr thr thr_term.
Proof.
  i. subst. inv H.
  econs; eauto. rewrite app_assoc in BASE. eauto.
Qed.

Lemma rtc_relax_base_cont:
  forall env tr thr thr_term c_base c_pfx c_sfx,
    Thread.rtc env c_base tr thr thr_term ->
    c_base = c_pfx ++ c_sfx ->
  Thread.rtc env c_sfx tr thr thr_term.
Proof.
  i. subst. induction H.
  { econs; eauto. }
  subst. eapply relax_base_cont in ONE; eauto. econs; eauto.
Qed.

Lemma seq_cases:
  forall env tr s_l s_r ts mmts thr_term,
    Thread.rtc env [] tr (Thread.mk (s_l ++ s_r) [] ts mmts) thr_term ->
  <<SEQ_LEFT_ONGOING:
    exists s_m c_m,
      Thread.rtc env [] tr
        (Thread.mk s_l [] ts mmts)
        (Thread.mk s_m c_m thr_term.(Thread.ts) thr_term.(Thread.mmts))
    /\ (thr_term.(Thread.stmt), thr_term.(Thread.cont)) = (s_m, c_m) ++₁ s_r
    /\ __guard__ (s_m <> [] \/ c_m <> [])>>
  \/
  <<SEQ_LEFT_DONE:
    exists ts0 mmts0 tr_l tr_r,
      tr = tr_l ++ tr_r
      /\ Thread.rtc env [] tr_l
        (Thread.mk s_l [] ts mmts)
        (Thread.mk [] [] ts0 mmts0)
      /\ Thread.rtc env [] tr_r
          (Thread.mk s_r [] ts0 mmts0)
          thr_term>>.
Proof.
  intros env tr s_l. revert env tr. induction s_l.
  { i. rewrite app_nil_l in H.
    right. esplits; eauto; try econs. ss.
  }
  i. inv H; ss.
  { left. esplits; try econs; eauto; ss. }
  inv ONE. inv NORMAL_STEP; inv STEP; ss; inv STMT.
  - hexploit IHs_l; eauto. i. des; [left | right]; esplits; eauto.
    + econs; eauto; [| rewrite app_nil_l]; ss.
      econs; eauto. try by econs; econs; eauto.
    + econs; eauto.
      { econs; eauto. try by econs; econs; eauto. }
      ss.
  - hexploit IHs_l; eauto. i. des; [left | right]; subst; esplits; eauto.
    + econs; eauto; [| instantiate (1 := [_])]; ss.
      econs; eauto. try by econs; econs; eauto.
    + instantiate (1 := _ :: _). ss.
    + econs; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; eauto. try by econs; econs; eauto.
  - hexploit IHs_l; eauto. i. des; [left | right]; subst; esplits; eauto.
    + econs; eauto; [| instantiate (1 := [_])]; ss.
      econs; eauto. try by econs; econs; eauto.
    + instantiate (1 := _ :: _). ss.
    + econs; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; eauto. try by econs; econs; eauto.
  - hexploit IHs_l; eauto. i. des; [left | right]; subst; esplits; eauto.
    + econs; eauto; [| instantiate (1 := [_])]; ss.
      econs; eauto. try by econs; econs; eauto.
    + instantiate (1 := _ :: _). ss.
    + econs; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; eauto. try by econs; econs; eauto.
  - hexploit IHs_l; eauto. i. des; [left | right]; subst; esplits; eauto.
    + econs; eauto; [| instantiate (1 := [_])]; ss.
      econs; eauto. try by econs; econs; eauto.
    + instantiate (1 := _ :: _). ss.
    + econs; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; eauto. try by econs; econs; eauto.
  - hexploit IHs_l; eauto. i. des; [left | right]; esplits; eauto.
    + econs; eauto; [| rewrite app_nil_l]; ss.
      econs; eauto. try by econs; econs; eauto.
    + econs; eauto.
      { econs; eauto. try by econs; econs; eauto. }
      ss.
  - hexploit chkpt_fn_cases; [| | left |]; eauto.
    { rewrite app_nil_l. ss. }
    i. des; ss.
    + left. esplits.
      * econs; [| | rewrite app_nil_l]; ss.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
        s. hexploit ongoing_cont_explosion; eauto; [rewrite app_nil_l|]; ss.
        intros LOOP_NEW. eapply rtc_relax_base_cont in LOOP_NEW; eauto.
        rewrite app_nil_r. ss.
      * rewrite seq_sc_last. ss.
        rewrite pair_equal_spec. ss.
      * right. destruct c_pfx; ss.
    + inv CALL_DONE2. inv ONE. inv NORMAL_STEP; inv STEP; ss; inv STMT; cycle 1.
      { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
        { ii. inv H. ss. }
        { ii. inv H. ss. }
        i. ss.
      }
      hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H. ss. }
      { ii. inv H. ss. }
      i. inv H. rewrite app_nil_r in *. subst.
      hexploit IHs_l; eauto. i. des; [left | right]; subst; esplits; cycle 3.
      { rewrite app_assoc. ss. }
      all: eauto.
      * eapply Thread.rtc_trans; eauto. econs.
        { econs; try by econs; econs; eauto. rewrite app_nil_r. ss. }
        all: cycle 1.
        { rewrite app_nil_l. ss. }
        s. rewrite <- (app_nil_r tr0).
        eapply Thread.rtc_trans.
        { hexploit ongoing_cont_explosion; eauto; ss.
          { rewrite app_nil_l. ss. }
          intros LOOP_NEW. eapply rtc_relax_base_cont; eauto.
          rewrite app_nil_r. ss.
        }
        econs.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto; ss. }
        { s. econs. }
        ss.
      * eapply Thread.rtc_trans; eauto. econs.
        { econs; try by econs; econs; eauto.
          rewrite app_nil_r. ss.
        }
        all: cycle 1.
        { rewrite app_nil_l. ss. }
        s. rewrite <- (app_nil_r tr0). eapply Thread.rtc_trans.
        { hexploit ongoing_cont_explosion; eauto; ss.
          { rewrite app_nil_l. ss. }
          intros LOOP_NEW. eapply rtc_relax_base_cont; eauto.
          rewrite app_nil_r. ss.
        }
        econs.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto; ss. }
        { s. econs. }
        ss.
  - destruct c_loops; ss.
  - hexploit IHs_l; eauto. i. des; [left | right]; esplits; eauto.
    + econs; eauto; [| rewrite app_nil_l]; ss.
      econs; eauto. try by econs; econs; eauto.
    + econs; eauto.
      { econs; eauto. try by econs; econs; eauto. }
      ss.
  - admit.
  - hexploit loop_cases; eauto.
    { rewrite app_nil_l. ss. }
    i. des.
    + assert (exists c_pfx, thr_term.(Thread.cont) = c_pfx ++ [Cont.loopcont (TState.regs ts) r s_body (s_l ++ s_r)]).
      { rewrite Thread.rtc_rtc' in LOOP_ONGOING. inv LOOP_ONGOING; ss.
        { exists []. rewrite app_nil_l. ss. }
        hexploit Thread.tc_last; eauto. i. des.
        inv H1. eauto.
      }
      des.
      s. left. esplits.
      * econs; [| | rewrite app_nil_l]; ss.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
        s. hexploit ongoing_cont_explosion; eauto; [rewrite app_nil_l|]; ss.
        intros LOOP_NEW. eapply rtc_relax_base_cont; eauto.
        rewrite app_nil_r. ss.
      * rewrite seq_sc_last. ss.
        rewrite pair_equal_spec. ss.
      * right. destruct c_pfx; ss.
    + subst. hexploit IHs_l; eauto. i. des; [left | right]; subst; esplits; cycle 3.
      { rewrite app_assoc. ss. }
      all: eauto.
      * eapply Thread.rtc_trans; eauto. econs.
        { econs; try by econs; econs; eauto. rewrite app_nil_r. ss. }
        all: cycle 1.
        { rewrite app_nil_l. ss. }
        s. rewrite <- (app_nil_r tr0).
        eapply Thread.rtc_trans.
        { hexploit ongoing_cont_explosion; eauto; try rewrite app_nil_l; ss.
          intros LOOP_NEW. eapply rtc_relax_base_cont; eauto.
          rewrite app_nil_r. ss.
        }
        econs.
        { econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss. }
        { s. econs. }
        ss.
      * eapply Thread.rtc_trans; eauto. econs.
        { econs; try by econs; econs; eauto. rewrite app_nil_r. ss. }
        all: cycle 1.
        { rewrite app_nil_l. ss. }
        s. rewrite <- (app_nil_r tr0). eapply Thread.rtc_trans.
        { hexploit ongoing_cont_explosion; eauto; try rewrite app_nil_l; ss.
          intros LOOP_NEW. eapply rtc_relax_base_cont; eauto.
          rewrite app_nil_r. ss.
        }
        econs.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
        { s. econs. }
        ss.
  - hexploit chkpt_fn_cases; [| | right |]; eauto.
    { rewrite app_nil_l. ss. }
    i. des; ss.
    + left. esplits.
      * econs; [| | rewrite app_nil_l]; ss.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
        s. hexploit ongoing_cont_explosion; eauto; [rewrite app_nil_l|]; ss.
        intros LOOP_NEW. eapply rtc_relax_base_cont in LOOP_NEW; eauto.
        rewrite app_nil_r. ss.
      * rewrite seq_sc_last. ss.
        rewrite pair_equal_spec. ss.
      * right. destruct c_pfx; ss.
    + inv CALL_DONE2. inv ONE. inv NORMAL_STEP; inv STEP; ss; inv STMT.
      { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
        { ii. inv H. ss. }
        { ii. inv H. ss. }
        i. ss.
      }
      hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H. ss. }
      { ii. inv H. ss. }
      i. inv H. rewrite app_nil_r in *. subst.
      hexploit IHs_l; eauto. i. des; [left | right]; subst; esplits; cycle 3.
      { rewrite app_assoc. ss. }
      all: eauto.
      * eapply Thread.rtc_trans; eauto. econs.
        { econs; try by econs; econs; eauto.
          rewrite app_nil_r. ss.
        }
        all: cycle 1.
        { rewrite app_nil_l. ss. }
        s. rewrite <- (app_nil_r tr0).
        eapply Thread.rtc_trans.
        { hexploit ongoing_cont_explosion; eauto; ss.
          { rewrite app_nil_l. ss. }
          intros LOOP_NEW. eapply rtc_relax_base_cont; eauto.
          rewrite app_nil_r. ss.
        }
        econs.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto; ss. }
        { s. econs. }
        ss.
      * eapply Thread.rtc_trans; eauto. econs.
        { econs; try by econs; econs; eauto.
          rewrite app_nil_r. ss.
        }
        all: cycle 1.
        { rewrite app_nil_l. ss. }
        s. rewrite <- (app_nil_r tr0). eapply Thread.rtc_trans.
        { hexploit ongoing_cont_explosion; eauto; ss.
          { rewrite app_nil_l. ss. }
          intros LOOP_NEW. eapply rtc_relax_base_cont; eauto.
          rewrite app_nil_r. ss.
        }
        econs.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto; ss. }
        { s. econs. }
        ss.
  - destruct c_loops; ss.
Qed.

Lemma lift_mmt:
  (* TODO: Define mid_pfx from ts.regs *)
  forall envt env labs s mid_pfx mids tr ts mmts thr_term,
    EnvType.rw_judge envt labs s ->
    mmt_id_exp mid_pfx labs = mids ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
  <<UNLIFT:
    Thread.rtc env [] tr
    (Thread.mk s [] ts (mmts |₁ mids))
    (Thread.mk thr_term.(Thread.stmt) thr_term.(Thread.cont) thr_term.(Thread.ts) (thr_term.(Thread.mmts) |₁ mids))>>
  /\
  <<COMPL_EQ:
    mmts |₁ (Complement _ mids) = thr_term.(Thread.mmts) |₁ (Complement _ mids)>>
  /\
  <<LIFT:
    forall mmts_a,
      Thread.rtc env [] tr
        (Thread.mk s [] ts ((mmts |₁ mids) ⊎ (mmts_a |₁ (Complement _ mids))))
        (Thread.mk thr_term.(Thread.stmt) thr_term.(Thread.cont) thr_term.(Thread.ts) ((thr_term.(Thread.mmts) |₁ mids) ⊎ (mmts_a |₁ (Complement _ mids))))>>.
Proof.
  intros envt env labs s mid_pfx mids tr ts mmts thr_term ENVT. revert mid_pfx mids tr ts mmts thr_term.
  induction ENVT; intros mid_pfx mids tr ts mmts thr_term EXP RTC; subst; ss.
  - inv RTC; ss.
    { splits; ss; try by econs; eauto. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv RTC; ss.
    { splits; ss; try by econs; eauto. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv RTC; ss.
    { splits; ss; try by econs; eauto. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv RTC; ss.
    { splits; ss; try by econs; eauto. }
    (* inv ONE. inv NORMAL_STEP; inv STEP; ss. *)
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.

Lemma lift_stmt_cons:
  forall env tr s c ts mmts thr_term c_pfx c_base s',
    Thread.rtc env c tr (Thread.mk s c ts mmts) thr_term ->
    c = c_pfx ++ [c_base] ->
  exists c_m c_term,
    Thread.rtc env c_m tr
      (Thread.mk s c_m ts mmts)
      (Thread.mk thr_term.(Thread.stmt) c_term thr_term.(Thread.ts) thr_term.(Thread.mmts))
    /\ c_m = c_pfx ++ [Cont.seq c_base s']
    /\ (thr_term.(Thread.stmt), c_term) = (thr_term.(Thread.stmt), thr_term.(Thread.cont)) ++₁ s'.
Proof.
  intros env tr s. revert env tr. induction s; i; ss.
  { inv H; ss.
    - esplits; eauto; try econs.
      rewrite seq_sc_last. ss.
    - inv ONE. inv NORMAL_STEP; inv STEP; ss.
  }
  inv H; ss.
  { esplits; try econs. rewrite seq_sc_last. ss. }
  inv ONE. inv NORMAL_STEP; inv STEP; ss; inv STMT.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_l]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_l]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_l]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_l]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_l]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_l]; ss. try by econs; econs; eauto. }
    ss.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.

Lemma lift_stmt_nil:
  forall env tr s ts mmts thr_term s',
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
  exists s_m c_m,
    Thread.rtc env [] tr
      (Thread.mk (s ++ s') [] ts mmts)
      (Thread.mk s_m c_m thr_term.(Thread.ts) thr_term.(Thread.mmts))
    /\ (s_m, c_m) = (thr_term.(Thread.stmt), thr_term.(Thread.cont)) ++₁ s'.
Proof.
  intros env tr s. revert env tr. induction s; i; ss.
  { hexploit stop_means_no_step; eauto.
    { s. unfold STOP. left. split; ss. }
    i. des. subst. s. unfold seq_sc. s. esplits; eauto. econs.
  }
  inv H; ss.
  { unfold seq_sc. s. esplits; eauto. econs. }
  inv ONE. rewrite app_nil_r in *. subst. inv NORMAL_STEP; inv STEP; ss; inv STMT.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
    ss.
  - hexploit chkpt_fn_cases; try exact RTC; try left; eauto.
    { rewrite app_nil_l. ss. }
    s. i. des.
    + hexploit lift_stmt_cons; eauto.
      { rewrite app_nil_l. ss. }
      s. i. des. subst. esplits; eauto.
      econs.
      * econs; try by econs; econs; eauto. rewrite app_nil_r. ss.
      * s. eapply rtc_relax_base_cont in H; eauto.
        rewrite app_nil_r. ss.
      * ss.
    + hexploit lift_stmt_cons; eauto.
      { rewrite app_nil_l. ss. }
      s. instantiate (1 := s'). i. des.
      rewrite seq_sc_last in *. apply pair_equal_spec in H1. des. subst. cleartriv.
      inv CALL_DONE2. inv ONE. inv NORMAL_STEP; inv STEP; ss; cycle 1.
      { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
        { ii. inv H0. ss. }
        { ii. inv H0. ss. }
        i. ss.
      }
      hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H0. ss. }
      { ii. inv H0. ss. }
      i. inv H0. rewrite app_nil_r in *. subst.
      rewrite snoc_eq_snoc in CONT. des. subst.
      hexploit IHs; eauto. i. des.
      esplits; eauto. eapply Thread.rtc_trans; eauto.
      rewrite <- (app_nil_r tr0). eapply Thread.rtc_trans; eauto.
      { econs.
        - econs; try by econs; econs; eauto. rewrite app_nil_r. ss.
        - s. eapply rtc_relax_base_cont in H; eauto.
          rewrite app_nil_r. ss.
        - ss.
      }
      econs; try by econs.
      { econs; try by econs; econs; eauto. rewrite app_nil_r. ss. }
      ss.
  - destruct c_loops; ss.
  - hexploit IHs; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
    ss.
  - admit.
    (* revert RTC. condtac; i.
    + hexploit seq_cases; eauto. i. des.
      * admit.
      * subst. hexploit IHs; eauto. i. des.
        esplits; eauto.
        eapply Thread.rtc_trans; eauto.
        econs; eauto. *)

  - admit.
  - hexploit chkpt_fn_cases; try exact RTC; try right; eauto.
    { rewrite app_nil_l. ss. }
    s. i. des.
    + hexploit lift_stmt_cons; eauto.
      { rewrite app_nil_l. ss. }
      s. i. des. subst. esplits; eauto.
      econs.
      * econs; try by econs; econs; eauto. rewrite app_nil_r. ss.
      * s. eapply rtc_relax_base_cont in H; eauto.
        rewrite app_nil_r. ss.
      * ss.
    + hexploit lift_stmt_cons; eauto.
      { rewrite app_nil_l. ss. }
      s. instantiate (1 := s'). i. des.
      rewrite seq_sc_last in *. apply pair_equal_spec in H1. des. subst. cleartriv.
      inv CALL_DONE2. inv ONE. inv NORMAL_STEP; inv STEP; ss.
      { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
        { ii. inv H0. ss. }
        { ii. inv H0. ss. }
        i. ss.
      }
      hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H0. ss. }
      { ii. inv H0. ss. }
      i. inv H0. rewrite app_nil_r in *. subst.
      rewrite snoc_eq_snoc in CONT. des. subst.
      hexploit IHs; eauto. i. des.
      esplits; eauto. eapply Thread.rtc_trans; eauto.
      rewrite <- (app_nil_r tr0). eapply Thread.rtc_trans; eauto.
      { econs.
        - econs; try by econs; econs; eauto. rewrite app_nil_r. ss.
        - s. eapply rtc_relax_base_cont in H; eauto.
          rewrite app_nil_r. ss.
        - ss.
      }
      econs; try by econs.
      { econs; try by econs; econs; eauto. rewrite app_nil_r. ss. }
      ss.
  - destruct c_loops; ss.
Qed.

Lemma lift_stmt:
  forall env tr s c ts mmts thr_term s',
    Thread.rtc env c tr (Thread.mk s c ts mmts) thr_term ->
  exists s0 c0 s1 c1,
    Thread.rtc env c0 tr
      (Thread.mk s0 c0 ts mmts)
      (Thread.mk s1 c1 thr_term.(Thread.ts) thr_term.(Thread.mmts))
    /\ (s0, c0) = (s, c) ++₁ s'
    /\ (s1, c1) = (thr_term.(Thread.stmt), thr_term.(Thread.cont)) ++₁ s'.
Proof.
  i. destruct c using rev_ind; ss.
  - hexploit lift_stmt_nil; eauto. i. des.
    esplits; eauto. ss.
  - hexploit lift_stmt_cons; eauto. i. des.
    esplits; eauto. subst. rewrite seq_sc_last. ss.
Qed.
