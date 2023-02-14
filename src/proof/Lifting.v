Require Import Ensembles.
Require Import EquivDec.
Require Import FunctionalExtensionality.
Require Import List.
Import ListNotations.

Require Import HahnList.
Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Order.
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

(* TODO: Drop c_base *)
Lemma chkpt_fn_cases:
  forall env c_base tr thr thr_term c c' c_sfx rmap r s_cont,
    Thread.rtc env c_base tr thr thr_term ->
    thr.(Thread.cont) = c ++ c' :: c_sfx ++ c_base ->
    ((exists mid_cont mid, c' = Cont.chkptcont rmap r s_cont mid_cont mid) \/ (exists mid_cont, c' = Cont.fncont rmap r s_cont mid_cont)) ->
  <<CALL_ONGOING:
    exists c_pfx,
      thr_term.(Thread.cont) = c_pfx ++ c' :: c_sfx ++ c_base
      /\ Thread.rtc env [] tr
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts))
      /\ Thread.rtc env (c' :: c_sfx ++ c_base) tr thr thr_term>>
  \/
  <<CALL_DONE:
    exists tr0 tr1 s_r c_r ts_r mmts_r e,
      tr = tr0 ++ tr1
      /\ Thread.rtc env [] tr0
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk ((stmt_return e) :: s_r) c_r ts_r mmts_r)
      /\ Thread.rtc env (c' :: c_sfx ++ c_base) tr0
          thr
          (Thread.mk ((stmt_return e) :: s_r) (c_r ++ c' :: c_sfx ++ c_base) ts_r mmts_r)
      /\ Thread.tc env c_base tr1 (Thread.mk ((stmt_return e) :: s_r) (c_r ++ c' :: c_sfx ++ c_base) ts_r mmts_r) thr_term
      /\ Cont.Loops c_r>>.
Proof.
  intros env c_base tr thr thr_term c c' c_sfx rmap r s_cont RTC. revert rmap r c c' c_sfx s_cont.
  induction RTC; i; subst.
  { left. esplits; eauto; econs; ss. }
  guardH H0.
  inversion ONE. inv NORMAL_STEP; inv STEP; ss.
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
    { rewrite app_comm_cons. eauto. }
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

    hexploit app_inv_tail. instantiate (1 := c_base).
    { repeat rewrite app_comm_cons in CONT. repeat rewrite app_assoc in CONT. exact CONT. }
    rename CONT into CONT2. intro CONT.

    assert (c'0 = c_sfx \/ exists c2', c'0 = c2' ++ c' :: c_sfx).
    { clear - c'0 CONT H0 LOOPS.
      rewrite app_comm_cons' in CONT. rewrite (app_comm_cons' _ _ c'0) in CONT. apply app_eq_app in CONT. des.
      - destruct l using rev_ind; [left | right]; ss.
        rewrite app_assoc in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
        rewrite <- app_assoc. eauto.
      - destruct l using rev_ind; [left | right]; ss.
        rewrite app_assoc in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
        repeat rewrite Cont.loops_app_distr in LOOPS; des. inv LOOPS1.
        unguard. des; subst; ss.
    }
    des; subst.
    + rewrite app_comm_cons' in CONT. rewrite (app_comm_cons' _ _ c_sfx) in CONT. apply app_inv_tail in CONT.
      rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. des; ss. inv H0.
      inv ONE.
      right. eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; try by econs; eauto.
      { rewrite app_nil_l. ss. }
      econs; eauto. econs; eauto.
    + hexploit IHRTC; eauto.
      { rewrite <- app_assoc. rewrite <- app_comm_cons. ss. }
      i. des.
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
    { rewrite app_comm_cons. eauto. }
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
    assert (c_rem = c_sfx ++ c_base \/ exists c_rem', c_rem = c_rem' ++ c' :: c_sfx ++ c_base).
    { destruct c; ss; inv CONT; eauto. }
    des; subst.
    { rewrite app_comm_cons' in CONT. rewrite <- app_nil_l in CONT. rewrite (app_comm_cons' _ _ (c_sfx ++ c_base)) in CONT.
      apply app_inv_tail in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. des; ss.
    }
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

    hexploit app_inv_tail. instantiate (1 := c_base).
    { repeat rewrite app_comm_cons in CONT. repeat rewrite app_assoc in CONT. exact CONT. }
    rename CONT into CONT2. intro CONT.

    assert (c'0 = c_sfx \/ exists c2', c'0 = c2' ++ c' :: c_sfx).
    { destruct c; ss; inv CONT; eauto. }
    des; subst.
    { rewrite app_comm_cons' in CONT. rewrite <- app_nil_l in CONT. rewrite (app_comm_cons' _ _ c_sfx) in CONT.
      apply app_inv_tail in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. des; ss.
    }
    hexploit IHRTC; eauto.
    { rewrite <- app_assoc. rewrite <- app_comm_cons. ss. }
    i. des.
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
    { rewrite app_comm_cons. eauto. }
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
    hexploit app_inv_tail. instantiate (1 := c_base).
    { repeat rewrite app_comm_cons in CONT. repeat rewrite app_assoc in CONT. exact CONT. }
    rename CONT into CONT2. intro CONT.

    assert (c'0 = c_sfx \/ exists c2', c'0 = c2' ++ c' :: c_sfx).
    { clear - c'0 CONT H0 LOOPS.
      rewrite app_comm_cons' in CONT. rewrite (app_comm_cons' _ _ c'0) in CONT. apply app_eq_app in CONT. des.
      - destruct l using rev_ind; [left | right]; ss.
        rewrite app_assoc in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
        rewrite <- app_assoc. eauto.
      - destruct l using rev_ind; [left | right]; ss.
        rewrite app_assoc in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
        repeat rewrite Cont.loops_app_distr in LOOPS; des. inv LOOPS1.
        unguard. des; subst; ss.
    }
    des; subst.
    + right.
      rewrite app_comm_cons' in CONT. rewrite (app_comm_cons' _ _ c_sfx) in CONT. apply app_inv_tail in CONT.
      rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. des; ss. inv H0.
      inv ONE.
      eexists. eexists. eexists. eexists. eexists. eexists. eexists. seqsplit; eauto; try by econs; eauto.
      { rewrite app_nil_l. ss. }
      econs; eauto. econs; eauto.
    + hexploit IHRTC; eauto.
      { rewrite <- app_assoc. rewrite <- app_comm_cons. ss. }
      i. des.
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
  forall env c_base tr thr thr_term c c' rmap r s_body s_cont,
    Thread.rtc env c_base tr thr thr_term ->
    thr.(Thread.cont) = c ++ [c'] ++ c_base ->
    c' = Cont.loopcont rmap r s_body s_cont ->
  <<LOOP_ONGOING: Thread.rtc env ([c'] ++ c_base) tr thr thr_term>>
  \/
  <<LOOP_DONE:
      exists tr0 tr1 s_r ts_r mmts_r,
        tr = tr0 ++ tr1
        /\ Thread.rtc env ([c'] ++ c_base) tr0
            thr
            (Thread.mk (stmt_break :: s_r) ([c'] ++ c_base) ts_r mmts_r)
        /\ Thread.rtc env c_base tr1
            (Thread.mk s_cont c_base (TState.mk rmap ts_r.(TState.time) ts_r.(TState.mid)) mmts_r)
            thr_term>>.
Proof.
  intros env c_base tr thr thr_term c c' rmap r s_body s_cont RTC. revert rmap r s_body s_cont c c'.
  induction RTC; i.
  { left. econs; ss. }
  guardH H0. subst.
  inversion ONE. inv NORMAL_STEP; inv STEP; ss.
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

    hexploit app_inv_tail. instantiate (1 := c_base).
    { repeat rewrite app_comm_cons in CONT. repeat rewrite app_assoc in CONT. rewrite app_comm_cons' in CONT. exact CONT. }
    rename CONT into CONT2. intro CONT.

    assert (c'0 = [] \/ exists c2', c'0 = c2' ++ [c']).
    { clear - c'0 CONT.
      destruct c'0 using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + right.
      rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. ss.
    + hexploit IHRTC; eauto.
      { rewrite <- app_assoc. rewrite <- app_comm_cons. ss. }
      i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss.
        { econs 8. econs; eauto; ss. }
        rewrite <- app_assoc. rewrite <- app_comm_cons. ss.
      * right. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss.
        { econs 8. econs; eauto; ss. }
        rewrite <- app_assoc. rewrite <- app_comm_cons. ss.
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
    assert (c_rem = c_base \/ exists c_rem', c_rem = c_rem' ++ [c'] ++ c_base).
    { destruct c; ss; inv CONT; eauto. }
    des; subst.
    + rewrite <- app_nil_l in CONT. rewrite app_comm_cons' in CONT. rewrite (app_comm_cons' _ []) in CONT. apply app_inv_tail in CONT.
      rewrite snoc_eq_snoc in CONT. des. subst.
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

    hexploit app_inv_tail. instantiate (1 := c_base).
    { repeat rewrite app_comm_cons in CONT. repeat rewrite app_assoc in CONT. rewrite app_comm_cons' in CONT. exact CONT. }
    rename CONT into CONT2. intro CONT.

    assert (c'0 = [] \/ exists c2', c'0 = c2' ++ [c']).
    { clear - c'0 CONT.
      destruct c'0 using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. inv H0. rewrite app_nil_l in *.
      right. esplits; eauto; [rewrite app_nil_l |]; ss.
      econs; eauto.
    + hexploit IHRTC; eauto.
      { rewrite <- app_assoc. rewrite <- app_comm_cons. ss. }
      i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss.
        { econs 13. econs; eauto; ss. }
        rewrite <- app_assoc. rewrite <- app_comm_cons. ss.
      * right. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss.
        { econs 13. econs; eauto; ss. }
        rewrite <- app_assoc. rewrite <- app_comm_cons. ss.
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

    hexploit app_inv_tail. instantiate (1 := c_base).
    { repeat rewrite app_comm_cons in CONT. repeat rewrite app_assoc in CONT. rewrite app_comm_cons' in CONT. exact CONT. }
    rename CONT into CONT2. intro CONT.

    assert (c'0 = [] \/ exists c2', c'0 = c2' ++ [c']).
    { clear - c'0 CONT.
      destruct c'0 using rev_ind; [left | right]; ss.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + right.
      rewrite snoc_eq_snoc in CONT. des. subst.
      unguard. ss.
    + hexploit IHRTC; eauto.
      { rewrite <- app_assoc. rewrite <- app_comm_cons. ss. }
      i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss.
        { econs 15. econs; eauto; ss. }
        rewrite <- app_assoc. rewrite <- app_comm_cons. ss.
      * right. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; ss.
        { econs 15. econs; eauto; ss. }
        rewrite <- app_assoc. rewrite <- app_comm_cons. ss.
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
            /\ ts1 = TState.mk (VRegMap.add r (sem_expr ts_r.(TState.regs) e) rmap) ts_r.(TState.time) ts_r.(TState.mid)>>
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
     (exists mid_cont mid,
        c' = Cont.chkptcont rmap r s_cont mid_cont mid
        /\ c0 = Cont.chkptcont rmap r s_cont0 mid_cont mid)
     \/
     (exists mid_cont,
        c' = Cont.fncont rmap r s_cont mid_cont
        /\ c0 = Cont.fncont rmap r s_cont0 mid_cont)
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
    { rewrite app_nil_l. s. instantiate (1 := []). ss. }
    i. des; ss.
    + left. esplits.
      * econs; [| | rewrite app_nil_l]; ss.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
        s. hexploit ongoing_cont_explosion; eauto; [rewrite app_nil_l | |]; ss.
        { right. left. eauto. }
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
          { right. left. eauto. }
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
          { right. left. eauto. }
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
  - (* TODO: if cases lemma 만들고 하면 될 것 같음. *)
    admit.
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
    { rewrite app_nil_l. s. instantiate (1 := []). ss. }
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

Lemma read_only_statements:
  forall env envt s tr ts mmts thr_term,
    EnvType.ro_judge envt s ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) thr_term ->
  [] ~ tr /\ mmts = thr_term.(Thread.mmts).
Proof.
  intros env envt s tr ts mmts thr_term ROJ. generalize tr ts mmts thr_term. induction ROJ; subst; i.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    split; ss. eapply refine_read; [apply trace_refine_eq |]; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss; cycle 1.
    { inv ONE. inv NORMAL_STEP; inv STEP; ss. }
    split; ss. eapply refine_read; [apply trace_refine_eq |]; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    hexploit loop_cases; eauto.
    { rewrite app_nil_l. ss. }
    i. des.
    + admit. (* TODO: induction이 안 됨. rtc [] 대신 rtc c를 해볼까? *)
    + admit.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inv RTC; ss.
    { split; ss. apply trace_refine_eq. }
    admit. (* TODO: RO 함수 호출하는 상황. DR_RW에서 쓰인 전제랑 비슷한 상황인 것 같음 *)
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss; destruct c_loops; inv CONT.
  - hexploit seq_cases; eauto. i. des.
    { apply IHROJ1 in SEQ_LEFT_ONGOING. ss. }
    subst. apply IHROJ1 in SEQ_LEFT_DONE0. apply IHROJ2 in SEQ_LEFT_DONE1. des. subst. split; ss.
    rewrite <- (app_nil_l []). apply trace_refine_app; ss.
  - inv H; ss.
    { split; ss. apply trace_refine_eq. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    inversion RTC; ss; subst.
    { split; ss. apply trace_refine_eq. }
    rewrite app_nil_r in *.
    destruct (EquivDec.equiv_dec (sem_expr (TState.regs ts0) e0) (Val.bool true)).
    + eapply IHROJ1; eauto.
    + eapply IHROJ2; eauto.
Qed.

(* TODO: admit 정리 *)
Lemma lift_mmt:
  forall envt env labs s mids tr ts mmts thr_term,
    EnvType.rw_judge envt labs s ->
    mmt_id_exp ts.(TState.mid) labs = mids ->
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
        (Thread.mk
          thr_term.(Thread.stmt)
          thr_term.(Thread.cont)
          thr_term.(Thread.ts)
          ((thr_term.(Thread.mmts) |₁ mids) ⊎ (mmts_a |₁ (Complement _ mids))))>>.
Proof.
  intros envt env labs s mids tr ts mmts thr_term ENVT. revert mids tr ts mmts thr_term.
  induction ENVT; intros mids tr ts mmts thr_term EXP RTC; subst; ss.
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
    inv ONE. inv NORMAL_STEP; inv STEP; ss; destruct c_loops; ss.
  - inv RTC; ss.
    { splits; ss; try by econs; eauto. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    hexploit stop_means_no_step; eauto; try by econs; ss. i. des. subst. ss.
    splits; ss.
    + econs; try by econs; econs; eauto.
      { econs; eauto. try by econs; econs; eauto. }
      ss.
    + i.
      econs; try by econs; econs; eauto.
      { econs; eauto. try by econs; econs; eauto. }
      ss.
  - inv RTC; ss.
    { splits; ss; try by econs; eauto. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss; inv STMT.
    + hexploit stop_means_no_step; eauto; try by econs; ss. i. des. subst. ss.
      splits; ss.
      * econs; try by econs; econs; eauto.
        all: cycle 1.
        { rewrite app_nil_r. ss. }
        econs; eauto. econs 4. econs; eauto; ss.
        { unfold Mmts.proj. condtac; ss.
          exfalso. apply n. econs; ss.
        }
        rewrite Mmts.proj_fun_add_eq; ss. econs; ss.
      * apply functional_extensionality. i. unfold Mmts.proj. condtac; ss.
        funtac. inversion e. subst.
        exfalso.
        unfold Ensembles.In in i. unfold Complement in i. apply i.
        econs; ss.
      * i.
        econs; try by econs; econs; eauto.
        all: cycle 1.
        { rewrite app_nil_r. ss. }
        econs; eauto. econs 4. econs; eauto; ss.
        { unfold Mmts.union. unfold Mmts.proj. condtac.
          { rewrite MMT. ss. }
          exfalso. apply n. econs; ss.
        }
        f_equal. apply functional_extensionality. i.
        funtac.
        -- inversion e. unfold Mmts.union. unfold Mmts.proj. condtac; funtac.
           exfalso. apply n. econs; ss.
        -- unfold Mmts.union. unfold Mmts.proj. condtac; funtac.
    + hexploit stop_means_no_step; eauto; try by econs; ss. i. des. subst. ss.
      splits; ss.
      * econs; try by econs; econs; eauto.
        all: cycle 1.
        { rewrite app_nil_r. ss. }
        econs; eauto. econs 5. econs; eauto; ss.
        { unfold Mmts.proj. condtac; ss.
          exfalso. apply n. econs; ss.
        }
        rewrite Mmts.proj_fun_add_eq; ss. econs; ss.
      * apply functional_extensionality. i. unfold Mmts.proj. condtac; ss.
        funtac. inversion e. subst.
        exfalso.
        unfold Ensembles.In in i. unfold Complement in i. apply i.
        econs; ss.
      * i.
        econs; try by econs; econs; eauto.
        all: cycle 1.
        { rewrite app_nil_r. ss. }
        econs; eauto. econs 5. econs; eauto; ss.
        { unfold Mmts.union. unfold Mmts.proj. condtac.
          { rewrite MMT. ss. }
          exfalso. apply n. econs; ss.
        }
        f_equal. apply functional_extensionality. i.
        funtac.
        -- inversion e. unfold Mmts.union. unfold Mmts.proj. condtac; funtac.
           exfalso. apply n. econs; ss.
        -- unfold Mmts.union. unfold Mmts.proj. condtac; funtac.
    + hexploit stop_means_no_step; eauto; try by econs; ss. i. des. subst. ss.
      splits; ss.
      * econs; try by econs; econs; eauto.
        { econs; eauto. econs 6. econs; eauto; ss.
          unfold Mmts.proj. condtac; ss.
          exfalso. apply n. econs; ss.
        }
        ss.
      * i.
        econs; try by econs; econs; eauto.
        { econs; eauto. econs 6. econs; eauto; ss.
          unfold Mmts.union. unfold Mmts.proj. condtac.
          { rewrite MMT. ss. }
          exfalso. apply n. econs; ss.
        }
        ss.
  - inv RTC; ss.
    { splits; ss; try by econs; eauto. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss; inv STMT.
    + hexploit chkpt_fn_cases; try exact RTC0; try left; eauto.
      { rewrite app_nil_l. s. instantiate (1 := []). ss. }
      i. des.
      * hexploit read_only_statements; try exact CALL_ONGOING0; eauto. s. i. des. rewrite <- H0 in *.
        admit.
      * admit.
    + hexploit stop_means_no_step; eauto; try by econs; ss. i. des. subst. ss.
      splits; ss.
      * econs; try by econs; econs; eauto.
        { econs; eauto. econs 9. econs; eauto; ss.
          unfold Mmts.proj. condtac; ss.
          exfalso. apply n. econs; ss.
        }
        ss.
      * i.
        econs; try by econs; econs; eauto.
        { econs; eauto. econs 9. econs; eauto; ss.
          unfold Mmts.union. unfold Mmts.proj. condtac.
          { rewrite MMT. ss. }
          exfalso. apply n. econs; ss.
        }
        ss.
  - admit.
  - inv RTC; ss.
    { splits; ss; try by econs; eauto. }
    inv ONE. inv NORMAL_STEP; inv STEP; ss. inv STMT.
    rewrite app_nil_r in *. destruct (sem_expr (TState.regs ts) e0 == Val.bool true).
    + hexploit IHENVT1; eauto. i. des. splits.
      * econs.
        { econs; [| rewrite app_nil_r]; ss. try by econs; econs; eauto. }
        all: cycle 1.
        { rewrite app_nil_l. ss. }
        condtac; ss. rewrite app_nil_r.
        admit.
        (* hexploit proj_union_exc_pres; eauto; ss.
        ii. inv H. econs; eauto. econs. ss. *)
      * apply functional_extensionality. i. unfold Mmts.proj. condtac; ss.
        apply equal_f with x in COMPL_EQ. revert COMPL_EQ.
        unfold Mmts.proj. condtac; ss.
        exfalso. apply n.
        generalize i. unfold Ensembles.In. unfold Complement. unfold Ensembles.In. ii. apply i0.
        clear - H. inv H. econs; eauto. econs. ss.
      * admit.
    + admit.
  - admit.
  - admit.
Qed.

Lemma lift_stmt_step:
  forall env c tr thr thr_term s',
    Thread.step_base_cont env c tr thr thr_term ->
  exists c_m s0 c0 s1 c1,
    Thread.step_base_cont env c_m tr
      (Thread.mk s0 c0 thr.(Thread.ts) thr.(Thread.mmts))
      (Thread.mk s1 c1 thr_term.(Thread.ts) thr_term.(Thread.mmts))
    /\ c_m = Cont.seql c s'
    /\ (s0, c0) = (thr.(Thread.stmt), thr.(Thread.cont)) ++₁ s'
    /\ (s1, c1) = (thr_term.(Thread.stmt), thr_term.(Thread.cont)) ++₁ s'.
Proof.
  i. inv H. inv NORMAL_STEP; inv STEP; ss; subst; rewrite STMT.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c'; ss. subst.
      esplits; eauto. econs; try by econs; econs; eauto.
      s. rewrite app_nil_l. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc.
        rewrite app_assoc in BASE. apply snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. eauto.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c'; ss. subst.
      esplits; eauto. econs; try by econs; econs; eauto.
      s. rewrite app_nil_l. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc.
        rewrite app_assoc in BASE. apply snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. eauto.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c'; ss. subst.
      esplits; eauto. econs; try by econs; econs; eauto.
      s. rewrite app_nil_l. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc.
        rewrite app_assoc in BASE. apply snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. eauto.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c'; ss. subst.
      esplits; eauto. econs; try by econs; econs; eauto.
      s. rewrite app_nil_l. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc.
        rewrite app_assoc in BASE. apply snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. eauto.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c'; ss. subst.
      esplits; eauto. econs; try by econs; econs; eauto.
      s. rewrite app_nil_l. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc.
        rewrite app_assoc in BASE. apply snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. eauto.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c'; ss. subst.
      esplits; eauto. econs; try by econs; econs; eauto.
      s. rewrite app_nil_l. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc.
        rewrite app_assoc in BASE. apply snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. eauto.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc. rewrite app_assoc in BASE. rewrite <- (app_nil_l [_]) in BASE. rewrite snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. rewrite <- BASE. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * rewrite app_nil_r in BASE. subst.
        esplits; eauto.
        { econs; try by econs; econs; eauto. s. rewrite app_nil_r. ss. }
        s. repeat rewrite app_comm_cons. rewrite seq_sc_last. ss.
      * clear IHc.
        rewrite app_comm_cons in BASE. rewrite app_assoc in BASE. rewrite snoc_eq_snoc in BASE. des. subst.
        esplits; eauto.
        { econs; try by econs; econs; eauto. s. rewrite app_comm_cons. rewrite BASE. rewrite Cont.seql_last. rewrite app_assoc. ss. }
        s. repeat rewrite app_comm_cons. rewrite seq_sc_last. ss.
  - rewrite CONT.
    destruct c using rev_ind; ss.
    + rewrite app_nil_r in *. destruct c' using rev_ind; ss.
      * rewrite seq_sc_last. unfold seq_sc. unfold seq_sc_unzip. ss.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_l. ss.
      * clear IHc'. repeat rewrite seq_sc_last.
        esplits; eauto.
        { econs; try by econs; econs; eauto. s. rewrite app_nil_r. ss. }
        s. rewrite STMT. repeat rewrite app_comm_cons. repeat rewrite app_assoc. rewrite seq_sc_last. ss.
    + clear IHc.
      repeat rewrite app_assoc. repeat rewrite seq_sc_last.
      esplits; eauto.
      { econs; try by econs; econs; eauto. s. rewrite Cont.seql_last. rewrite app_assoc. ss. }
      s. rewrite STMT. repeat rewrite app_comm_cons. repeat rewrite app_assoc. rewrite seq_sc_last. ss.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c'; ss. subst.
      esplits; eauto. econs; try by econs; econs; eauto.
      s. rewrite app_nil_l. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc.
        rewrite app_assoc in BASE. apply snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. eauto.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c'; ss. subst.
      esplits; eauto.
      econs; cycle 1.
      { s. rewrite app_nil_l. ss. }
      econs 10. econs; ss. rewrite app_assoc. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc.
        rewrite app_assoc in BASE. apply snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. eauto.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc. rewrite app_assoc in BASE. rewrite <- (app_nil_l [_]) in BASE. rewrite snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. rewrite <- BASE. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * rewrite app_nil_r in BASE. subst.
        esplits; eauto.
        { econs; try by econs; econs; eauto. s. rewrite app_nil_r. ss. }
        s. repeat rewrite app_comm_cons. rewrite seq_sc_last. ss.
      * clear IHc.
        rewrite app_comm_cons in BASE. rewrite app_assoc in BASE. rewrite snoc_eq_snoc in BASE. des. subst.
        esplits; eauto.
        { econs; try by econs; econs; eauto. s. rewrite app_comm_cons. rewrite BASE. rewrite Cont.seql_last. rewrite app_assoc. ss. }
        s. repeat rewrite app_comm_cons. rewrite seq_sc_last. ss.
  - rewrite CONT.
    destruct c_rem using rev_ind; ss.
    + rewrite <- (app_nil_l [_]). rewrite seq_sc_last. unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc. destruct thr. ss. destruct cont using rev_ind; ss. clear IHcont.
        rewrite app_assoc in BASE. rewrite snoc_eq_snoc in BASE. des. subst.
        rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. unfold Cont.seq.
        rewrite app_assoc. rewrite CONT. ss.
    + clear IHc_rem.
      repeat rewrite app_assoc. rewrite app_comm_cons. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * esplits; eauto.
        econs; try by econs; econs; eauto. s. rewrite app_nil_r. ss.
      * clear IHc. rewrite BASE in CONT. rewrite app_comm_cons in CONT. rewrite app_assoc in CONT. rewrite snoc_eq_snoc in CONT. des. subst.
        esplits; eauto.
        econs; try by econs; econs; eauto. s. rewrite Cont.seql_last.
        rewrite app_assoc. rewrite CONT. ss.
  - rewrite CONT.
    destruct c using rev_ind; ss.
    + rewrite app_nil_r in *. destruct c' using rev_ind; ss.
      * rewrite <- (app_nil_l [_]). rewrite seq_sc_last. unfold seq_sc. unfold seq_sc_unzip. ss.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_l. ss.
      * clear IHc'. repeat rewrite seq_sc_last.
        esplits; eauto.
        { econs; [| rewrite app_nil_r]; ss.
          econs 13. econs; ss.
        }
        rewrite (app_comm_cons _ [x]). rewrite seq_sc_last. ss.
    + clear IHc.
      repeat rewrite app_assoc. rewrite app_comm_cons. repeat rewrite seq_sc_last.
      esplits; eauto.
      econs; try by econs; econs; eauto. s. rewrite Cont.seql_last. rewrite app_assoc. ss.
  - destruct thr. ss. destruct cont using rev_ind.
    + unfold seq_sc. unfold seq_sc_unzip. ss.
      destruct c using rev_ind; ss.
      * esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_r. ss.
      * clear IHc. rewrite app_assoc in BASE. rewrite <- (app_nil_l [_]) in BASE. rewrite snoc_eq_snoc in BASE. des. subst.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite Cont.seql_last. rewrite app_assoc. rewrite <- BASE. ss.
    + clear IHcont. repeat rewrite seq_sc_last.
      destruct c using rev_ind; ss.
      * rewrite app_nil_r in BASE. subst.
        esplits; eauto.
        { econs; try by econs; econs; eauto. s. rewrite app_nil_r. ss. }
        s. repeat rewrite app_comm_cons. rewrite seq_sc_last. ss.
      * clear IHc.
        rewrite app_comm_cons in BASE. rewrite app_assoc in BASE. rewrite snoc_eq_snoc in BASE. des. subst.
        esplits; eauto.
        { econs; try by econs; econs; eauto. s. rewrite app_comm_cons. rewrite BASE. rewrite Cont.seql_last. rewrite app_assoc. ss. }
        s. repeat rewrite app_comm_cons. rewrite seq_sc_last. ss.
  - rewrite CONT.
    destruct c using rev_ind; ss.
    + rewrite app_nil_r in *. destruct c' using rev_ind; ss.
      * rewrite seq_sc_last. unfold seq_sc. unfold seq_sc_unzip. ss.
        esplits; eauto. econs; try by econs; econs; eauto.
        s. rewrite app_nil_l. ss.
      * clear IHc'. repeat rewrite seq_sc_last.
        esplits; eauto.
        { econs.
          { econs 15. econs; try exact LOOPS; ss. }
          s. rewrite app_nil_r. ss.
        }
        rewrite (app_comm_cons _ [x]). rewrite app_assoc. rewrite seq_sc_last.
        rewrite (app_comm_cons c'). rewrite app_assoc. ss.
    + clear IHc.
      repeat rewrite app_assoc. repeat rewrite seq_sc_last.
      esplits; eauto.
      { econs.
          { econs 15. econs; try exact LOOPS; ss. }
          s. rewrite Cont.seql_last. rewrite app_assoc. ss.
      }
      rewrite (app_comm_cons _ [x]). rewrite app_assoc. rewrite seq_sc_last.
      rewrite (app_comm_cons' _ c_loops). rewrite app_assoc. rewrite app_assoc.
      rewrite (app_comm_cons _ c). rewrite app_assoc. symmetry. rewrite (app_comm_cons' _ c_loops). ss.
Qed.

Lemma lift_stmt:
  forall env c tr thr thr_term s',
    Thread.rtc env c tr thr thr_term ->
  exists c_m s0 c0 s1 c1,
    Thread.rtc env c_m tr
      (Thread.mk s0 c0 thr.(Thread.ts) thr.(Thread.mmts))
      (Thread.mk s1 c1 thr_term.(Thread.ts) thr_term.(Thread.mmts))
    /\ c_m = Cont.seql c s'
    /\ (s0, c0) = (thr.(Thread.stmt), thr.(Thread.cont)) ++₁ s'
    /\ (s1, c1) = (thr_term.(Thread.stmt), thr_term.(Thread.cont)) ++₁ s'.
Proof.
  intros env tr c thr thr_term s' RTC. revert s'.
  induction RTC.
  { i. destruct thr. ss. destruct cont using rev_ind; ss.
    { esplits; eauto; try econs. }
    rewrite seq_sc_last. esplits; eauto; try econs.
  }
  i. subst.
  hexploit lift_stmt_step; eauto. instantiate (1 := s'). i. des. subst.
  hexploit IHRTC; eauto.
  instantiate (1 := s'). i. des. subst.
  rewrite <- H2 in H4. rewrite pair_equal_spec in *. des. subst.
  esplits; eauto. eapply Thread.rtc_trans; eauto. econs; eauto; try econs.
  rewrite app_nil_r. ss.
Qed.

Lemma mid_flat_eq:
  forall env c tr s ts mmts thr_term loops_term,
    Thread.rtc env c tr (Thread.mk s c ts mmts) thr_term ->
    thr_term.(Thread.cont) = loops_term ++ c ->
    Cont.Loops loops_term ->
  ts.(TState.mid) = thr_term.(Thread.ts).(TState.mid).
Proof.
  intros env c tr s. revert env c tr.
  induction s; i; subst.
  { inv H; ss. inv ONE; inv NORMAL_STEP; inv STEP; ss. }
  inv H; ss.
  inversion ONE. inv NORMAL_STEP; inv STEP; ss; inv STMT.
  all: try by hexploit IHs; try exact RTC; try exact H0; ss.
  - (* CHKPT-CALL *)
    hexploit chkpt_fn_cases; try exact RTC; try left; eauto.
    { rewrite app_nil_l. s. instantiate (1 := []). ss. }
    s. i. des.
    { (* CALL-ONGOING *)
      clear - CALL_ONGOING H0 H1.
      rewrite H0 in CALL_ONGOING. rewrite app_comm_cons' in CALL_ONGOING. apply app_inv_tail in CALL_ONGOING. subst.
      apply Cont.loops_app_distr in H1. des. inv H2. ss.
    }
    (* CALL-DONE *)
    subst. inv CALL_DONE2. inv ONE0. inv NORMAL_STEP; inv STEP; ss; inv STMT; cycle 1.
    { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H. ss. }
      { ii. inv H. ss. }
      i. ss.
    }
    hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
    { ii. inv H. ss. }
    { ii. inv H. ss. }
    intro CONT_EQ. inv CONT_EQ.

    hexploit app_inv_tail.
    { rewrite app_nil_l. exact H7. }
    i. subst. rewrite app_nil_l in *. cleartriv.
    hexploit IHs; eauto.
  - (* CHKPT-RET *)
    rewrite app_comm_cons in CONT. rewrite app_assoc in CONT. hexploit app_inv_tail.
    { rewrite app_nil_l. eauto. }
    i. destruct c_loops; ss.
  - (* IF *)
    admit.
  - (* LOOP *)
    admit.
  - (* CONTINUE *)
    admit.
  - (* BREAK *)
    rewrite app_comm_cons in CONT. hexploit app_inv_tail.
    { rewrite app_nil_l. eauto. }
    ss.
  - (* FN-CALL *)
    hexploit chkpt_fn_cases; try exact RTC; try right; eauto.
    { rewrite app_nil_l. s. instantiate (1 := []). ss. }
    s. i. des.
    { (* CALL-ONGOING *)
      clear - CALL_ONGOING H0 H1.
      rewrite H0 in CALL_ONGOING. rewrite app_comm_cons' in CALL_ONGOING. apply app_inv_tail in CALL_ONGOING. subst.
      apply Cont.loops_app_distr in H1. des. inv H2. ss.
    }
    (* CALL-DONE *)
    subst. inv CALL_DONE2. inv ONE0. inv NORMAL_STEP; inv STEP; ss; inv STMT.
    { hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
      { ii. inv H. ss. }
      { ii. inv H. ss. }
      i. ss.
    }
    hexploit Cont.loops_base_cont_eq; try exact CONT; eauto.
    { ii. inv H. ss. }
    { ii. inv H. ss. }
    intro CONT_EQ. inv CONT_EQ.

    hexploit app_inv_tail.
    { rewrite app_nil_l. exact H6. }
    i. subst. rewrite app_nil_l in *. cleartriv.
    hexploit IHs; eauto.
  - (* FN-RET *)
    rewrite app_comm_cons in CONT. rewrite app_assoc in CONT. hexploit app_inv_tail.
    { rewrite app_nil_l. eauto. }
    i. destruct c_loops; ss.
Qed.
