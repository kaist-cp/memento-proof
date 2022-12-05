Require Import List.
Import ListNotations.

Require Import HahnList.
Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Common.

Set Implicit Arguments.

Lemma chkpt_fn_cases:
  forall env tr thr thr_term c c' rmap r,
    Thread.rtc env [] tr thr thr_term ->
    thr.(Thread.cont) = c ++ [c'] ->
    ((exists mid, c' = Cont.chkptcont rmap r [] mid) \/ c' = Cont.fncont rmap r []) ->
  <<CALL_ONGOING:
    exists c_pfx, thr_term.(Thread.cont) = c_pfx ++ [c']
    /\ Thread.rtc env [] tr
        (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
        (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts))>>
  \/
  <<CALL_DONE:
    exists s_r c_r ts_r mmts_r e,
      Thread.rtc env [] tr
        (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
        (Thread.mk ((stmt_return e) :: s_r) c_r ts_r mmts_r)
      /\ Thread.step env [] (Thread.mk ((stmt_return e) :: s_r) (c_r ++ [c']) ts_r mmts_r) thr_term
      /\ thr_term.(Thread.stmt) = [] /\ thr_term.(Thread.cont) = []
      /\ (c' = Cont.fncont rmap r [] -> thr_term.(Thread.mmts) = mmts_r)>>.
Proof.
  intros env tr thr thr_term c c' rmap r RTC. revert rmap r c c'.
  induction RTC; i; subst.
  { left. esplits; eauto. econs; ss. }
  guardH H0.
  inversion ONE. rewrite app_nil_r in *. subst. inv NORMAL_STEP; inv STEP; ss.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 2. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 2. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 3. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 3. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 4. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 4. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 5. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 5. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 6. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 6. econs; eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 7. econs; eauto. ss.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 7. econs; eauto. ss.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [c']).
    { clear - c2 CONT.
      hexploit list_construct_app. instantiate (4 := c2). i. des; [left | right]; ss. subst.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + right.
      rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. des; ss. inv H0.
      hexploit stop_means_no_step; eauto.
      { econs; eauto. }
      i. inv H. ss. inv ONE. esplits; [econs | | | |]; eauto.
      i. ss.
    + hexploit IHRTC; eauto. i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 8. econs; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
      * right. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 8. econs; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 9. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 9. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 10. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 10. econs; eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 11. econs; eauto. ss.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 11. econs; eauto. ss.
  - destruct thr. ss. subst.
    assert (c_rem = [] \/ exists c_rem', c_rem = c_rem' ++ [c']).
    { clear - c_rem CONT.
      hexploit list_construct_app. instantiate (4 := c_rem). i. des; [left | right]; ss. subst.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    { unguard. rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des; subst; ss. }
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 12. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 12. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [c']).
    { clear - c2 CONT.
      hexploit list_construct_app. instantiate (4 := c2). i. des; [left | right]; ss. subst.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. ss. inv CONT.
      esplits. eauto.
    }
    des; subst.
    { unguard. rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des; subst; ss. }
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 14. econs; eauto; ss.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 14. econs; eauto. ss.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [c']).
    { clear - c2 CONT.
      hexploit list_construct_app. instantiate (4 := c2). i. des; [left | right]; ss. subst.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + right.
      rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. des; ss. inv H0.
      hexploit stop_means_no_step; eauto.
      { econs; eauto. }
      i. inv H. ss. esplits; eauto.
      { econs; eauto. }
      inv ONE. eauto.
    + hexploit IHRTC; eauto. i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 15. econs; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
      * right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 15. econs; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
Qed.

Lemma loop_cases:
  forall env tr thr thr_term c c' c_sfx rmap r s,
    Thread.rtc env [] tr thr thr_term ->
    thr.(Thread.cont) = c ++ c' :: c_sfx ->
    c' = Cont.loopcont rmap r s [] ->
  <<LOOP_ONGOING: Thread.rtc env (c' :: c_sfx) tr thr thr_term>>
  \/
  <<LOOP_DONE:
      exists s_r ts_r,
        Thread.rtc env (c' :: c_sfx) tr
          thr
          (Thread.mk (stmt_break :: s_r) (c' :: c_sfx) ts_r thr_term.(Thread.mmts))
        /\ thr_term.(Thread.stmt) = []
        /\ thr_term.(Thread.cont) = c_sfx
        /\ thr_term.(Thread.ts) = TState.mk rmap ts_r.(TState.time)>>.
Proof.
  intros env tr thr thr_term c c' c_sfx rmap r s RTC. revert rmap r s c c' c_sfx.
  induction RTC; i.
  { left. econs; ss. }
  guardH H0. subst.
  inversion ONE. rewrite app_nil_r in *. subst. inv NORMAL_STEP; inv STEP; ss.
  - hexploit IHRTC; eauto. i. des.
    + left. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 2. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 2. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 3. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 3. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 4. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 4. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 5. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 5. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs 6. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite H]; ss. econs 6. econs; eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (2 := _ :: _). ss. }
    i. des.
    + left.
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
    assert (c2 = c_sfx \/ exists c2', c2 = c2' ++ c' :: c_sfx).
    { clear - c2 CONT.
      admit.
    }
    des; subst.
    + right. rewrite app_comm_cons' in CONT. symmetry in CONT. rewrite app_comm_cons' in CONT.
      apply app_inv_tail in CONT.
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
    { instantiate (2 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss. econs 11. econs; eauto; ss.
      instantiate (1 := _ :: _). ss.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss. econs 11. econs; eauto; ss.
      instantiate (1 := _ :: _). ss.
  - destruct thr. ss. subst.
    assert (c_rem = c_sfx \/ exists c_rem', c_rem = c_rem' ++ c' :: c_sfx).
    { clear - c_rem CONT.
      admit.
    }
    des; subst.
    + rewrite <- app_nil_l in CONT. rewrite app_comm_cons' in CONT. symmetry in CONT. rewrite app_comm_cons' in CONT.
      apply app_inv_tail in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
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
    assert (c2 = c_sfx \/ exists c2', c2 = c2' ++ c' :: c_sfx).
    { clear - c2 CONT.
      admit.
    }
    des; subst.
    + rewrite <- app_nil_l in CONT. rewrite app_comm_cons' in CONT. symmetry in CONT. rewrite app_comm_cons' in CONT.
      apply app_inv_tail in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. inv H0. rewrite app_nil_l in *.
      hexploit stop_means_no_step; eauto.
      { econs; eauto. }
      i. inv H. ss.
      right. esplits; eauto.
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
    { instantiate (2 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss. econs 14. econs; eauto; ss.
      instantiate (1 := _ :: _). ss.
    + right. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; ss. econs 14. econs; eauto; ss.
      instantiate (1 := _ :: _). ss.
  - destruct thr. ss. subst.
    assert (c2 = c_sfx \/ exists c2', c2 = c2' ++ c' :: c_sfx).
    { clear - c2 CONT.
      admit.
    }
    des; subst.
    + right.
      rewrite app_comm_cons' in CONT. symmetry in CONT. rewrite app_comm_cons' in CONT.
      apply app_inv_tail in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
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

Inductive first_loop_iter_ind (env: Env.t) (c: Cont.t): list Event.t -> Thread.t -> Thread.t -> Prop :=
| first_ongoing
  c' c_pfx tr thr thr_term
  (CONT: thr.(Thread.cont) = c' ++ [c])
  (C_PFX: thr_term.(Thread.cont) = c_pfx ++ [c])
  (RTC: Thread.rtc env [] tr
          (Thread.mk thr.(Thread.stmt) c' thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts)))
  : first_loop_iter_ind env c tr thr thr_term
| first_done
  tr thr thr_term
  tr1 tr2 c' e s1 ts1 mmts1
  (CONT: thr.(Thread.cont) = c' ++ [c])
  (TRACE: tr = tr1 ++ tr2)
  (ITER: Thread.rtc env [] tr1
          (Thread.mk thr.(Thread.stmt) c' thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk ((stmt_continue e) :: s1) [] ts1 mmts1))
  (NEXT: first_loop_iter_ind env c tr2 (Thread.mk ((stmt_continue e) :: s1) [c] ts1 mmts1) thr_term)
  : first_loop_iter_ind env c tr thr thr_term
.

Lemma first_loop_iter2:
  forall env tr thr thr_term c c' rmap r s,
    Thread.rtc env [c'] tr thr thr_term ->
    thr.(Thread.cont) = c ++ [c'] ->
    c' = Cont.loopcont rmap r s [] ->
  first_loop_iter_ind env c' tr thr thr_term.
Proof.
  admit.
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
