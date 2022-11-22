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
  forall env c_base tr thr thr_term c c' rmap r,
    c_base = [] ->
    Thread.rtc env tr thr thr_term c_base ->
    thr.(Thread.cont) = c ++ [c'] ->
    ((exists mid, c' = Cont.chkptcont rmap r [] mid) \/ c' = Cont.fncont rmap r []) ->
  <<CALL_ONGOING:
    exists c_pfx, thr_term.(Thread.cont) = c_pfx ++ [c']
    /\ Thread.rtc env tr
        (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
        (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts))
        []>>
  \/
  <<CALL_DONE:
    exists s_r c_r ts_r mmts_r e,
      Thread.rtc env tr (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts)) (Thread.mk ((stmt_return e) :: s_r) c_r ts_r mmts_r) []
      /\ Thread.step env [] (Thread.mk ((stmt_return e) :: s_r) (c_r ++ [c']) ts_r mmts_r) thr_term
      /\ thr_term.(Thread.stmt) = [] /\ thr_term.(Thread.cont) = []
      /\ (c' = Cont.fncont rmap r [] -> thr_term.(Thread.mmts) = mmts_r)>>.
Proof.
  intros env c_base tr thr thr_term c c' rmap r EMPTY RTC.
  generalize dependent rmap. generalize dependent r. generalize dependent c. generalize dependent c'.
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
  forall env c_base tr thr thr_term c c' rmap r s,
    c_base = [] ->
    Thread.rtc env tr thr thr_term c_base ->
    thr.(Thread.cont) = c ++ [c'] ->
    c' = Cont.loopcont rmap r s [] ->
  <<LOOP_ONGOING: Thread.rtc env tr thr thr_term [c']>>
  \/
  <<LOOP_DONE:
      exists s_r ts_r,
        Thread.rtc env tr
          thr
          (Thread.mk (stmt_break :: s_r) [c'] ts_r thr_term.(Thread.mmts))
          [c']
        /\ thr_term.(Thread.stmt) = []
        /\ thr_term.(Thread.cont) = []
        /\ thr_term.(Thread.ts) = TState.mk rmap ts_r.(TState.time)>>.
Proof.
  intros env c_base tr thr thr_term c c' rmap r s EMPTY RTC.
  generalize dependent rmap. generalize dependent r. generalize dependent s. generalize dependent c. generalize dependent c'.
  induction RTC; i.
  { left. esplits; eauto. econs; ss. }
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
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 2. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 3. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 3. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 4. econs; eauto.
    + right. esplits; eauto.
      econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 4. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite H]; ss. econs 5. econs; eauto.
    + right. esplits; eauto.
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
      hexploit list_construct_app. instantiate (4 := c2). i. des; [left | right]; ss. subst.
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
      hexploit list_construct_app. instantiate (4 := c_rem). i. des; [left | right]; ss. subst.
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
      hexploit list_construct_app. instantiate (4 := c2). i. des; [left | right]; ss. subst.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
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
      hexploit list_construct_app. instantiate (4 := c2). i. des; [left | right]; ss. subst.
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
    Thread.rtc env tr thr thr_term [c'] ->
    thr.(Thread.cont) = c ++ [c'] ->
    c' = Cont.loopcont rmap r s [] ->
  <<FIRST_ONGOING:
      exists c_pfx, thr_term.(Thread.cont) = c_pfx ++ [c']
        /\ Thread.rtc env tr
            (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
            (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts))
            []>>
  \/
  <<FIRST_DONE:
    exists tr1 tr2 e s1 ts1 mmts1,
      tr = tr1 ++ tr2
      /\ Thread.rtc env tr1
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk ((stmt_continue e) :: s1) [] ts1 mmts1)
          []
      /\ Thread.rtc env tr2
          (Thread.mk ((stmt_continue e) :: s1) [c'] ts1 mmts1)
          thr_term
          [c']>>.
Proof.
  admit.
Qed.

Lemma last_loop_iter:
  forall env tr thr thr_term c c' rmap r s,
    Thread.rtc env tr thr thr_term [c'] ->
    thr.(Thread.cont) = c ++ [c'] ->
    c' = Cont.loopcont rmap r s [] ->
  exists tr1 tr2 s1 c1 ts1 mmts1 c_pfx,
    tr = tr1 ++ tr2
    /\ __guard__(<<LAST_FIRST:
          s1 = thr.(Thread.stmt) /\ c1 = c
          /\ ts1 = thr.(Thread.ts) /\ mmts1 = thr.(Thread.mmts)
          /\ tr1 = []>>
       \/
       <<LAST_CONT:
          exists e s_r ts_r,
            Thread.rtc env tr1
              thr
              (Thread.mk ((stmt_continue e) :: s_r) [c'] ts_r mmts1)
              [c']
            /\ s1 = s
            /\ c1 = []
            /\ ts1 = TState.mk (VRegMap.add r (sem_expr ts_r.(TState.regs) e) rmap) ts_r.(TState.time)>>)
    /\ thr_term.(Thread.cont) = c_pfx ++ [c']
    /\ Thread.rtc env tr2
          (Thread.mk s1 c1 ts1 mmts1)
          (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts))
          [].
Proof.
  admit.
Qed.
