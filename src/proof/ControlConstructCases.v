Require Import Lia.
Require Import List.
Import ListNotations.

Require Import HahnList.
Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Common.

Set Implicit Arguments.

Lemma checkpoint_cont_unlift :
  forall env tr thr thr_term c_base rmap r s mid c_sfx,
    c_base = (Cont.chkptcont rmap r s mid) :: c_sfx ->
    Thread.rtc env tr thr thr_term c_base ->
  Thread.rtc env tr thr thr_term [].
Proof.
  i. induction H0; subst; [econs |]; ss.
  hexploit IHrtc; eauto. i. econs 2; eauto.
  inv ONE. inversion NORMAL_STEP; inv STEP; econs; eauto; ss.
  all: rewrite app_nil_r; eauto.
Qed.

Lemma checkpoint_cases :
  forall env c_base tr thr thr_term c rmap r mid,
    c_base = [] ->
    Thread.rtc env tr thr thr_term c_base ->
    thr.(Thread.cont) = c ++ [Cont.chkptcont rmap r [] mid] ->
  <<CALL_ONGOING:
    exists c_pfx, thr_term.(Thread.cont) = c_pfx ++ [Cont.chkptcont rmap r [] mid]
    /\ Thread.rtc env tr
        (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
        (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts))
        []>>
  \/
  <<CALL_DONE:
    exists s_r c_r ts_r mmts_r e,
      Thread.rtc env tr (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts)) (Thread.mk ((stmt_return e) :: s_r) c_r ts_r mmts_r) []
      /\ Thread.step env [] (Thread.mk ((stmt_return e) :: s_r) (c_r ++ [Cont.chkptcont rmap r [] mid]) ts_r mmts_r) thr_term
      /\ thr_term.(Thread.stmt) = [] /\ thr_term.(Thread.cont) = []>>.
Proof.
  intros env c_base tr thr thr_term c rmap r mid EMPTY RTC.
  generalize dependent rmap. generalize dependent r. generalize dependent mid. generalize dependent c.
  induction RTC; i; subst.
  { left. esplits; eauto. econs; ss. }
  inversion ONE. rewrite app_nil_r in *. subst. inv NORMAL_STEP; inv STEP; ss.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs. econs; eauto.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 2. econs; eauto.
    + right. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 2. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 3. econs; eauto.
    + right. esplits; eauto. econs 2; eauto; cycle 1.
      { instantiate (1 := [_]). ss. }
      econs; [| rewrite app_nil_r]; ss. econs 3. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 4. econs; eauto.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 4. econs; eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (1 := mid). instantiate (1 := r). instantiate (1 := rmap). instantiate (1 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto.
      econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 5. econs; eauto. ss.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 5. econs; eauto. ss.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [Cont.chkptcont rmap r [] mid]).
    { clear - c2 CONT.
      hexploit list_construct_app. instantiate (4 := c2). i. des; [left | right]; ss. subst.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    + right.
      rewrite snoc_eq_snoc in CONT. des. subst. inv CONT0.
      hexploit stop_means_no_step; eauto.
      { econs; eauto. }
      i. inv H. ss. esplits; eauto.
      { econs; eauto. }
      inv ONE. eauto.
    + hexploit IHRTC; eauto. i. des.
      * left. esplits; eauto.
        econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 6. econs; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
      * right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
        econs; [| rewrite app_nil_r]; ss. econs 6. econs; eauto; ss.
        rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 7. econs; eauto.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 7. econs; eauto.
  - hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 8. econs; eauto.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 8. econs; eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (4 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 9. econs; eauto. ss.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 9. econs; eauto. ss.
  - destruct thr. ss. subst.
    assert (c_rem = [] \/ exists c_rem', c_rem = c_rem' ++ [Cont.chkptcont rmap r [] mid]).
    { clear - c_rem CONT.
      hexploit list_construct_app. instantiate (4 := c_rem). i. des; [left | right]; ss. subst.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    { rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des. ss. }
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 10. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 10. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [Cont.chkptcont rmap r [] mid]).
    { clear - c2 CONT.
      hexploit list_construct_app. instantiate (4 := c2). i. des; [left | right]; ss. subst.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. ss. inv CONT.
      esplits. eauto.
    }
    des; subst.
    { rewrite <- app_nil_l in CONT. rewrite snoc_eq_snoc in CONT. des. ss. }
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 11. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 11. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. eauto.
  - destruct thr. ss. subst.
    hexploit IHRTC; eauto.
    { instantiate (4 := _ :: _). ss. }
    i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 12. econs; eauto; ss.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 12. econs; eauto. ss.
  - destruct thr. ss. subst.
    assert (c2 = [] \/ exists c2', c2 = c2' ++ [Cont.chkptcont rmap r [] mid]).
    { clear - c2 CONT.
      hexploit list_construct_app. instantiate (4 := c2). i. des; [left | right]; ss. subst.
      rewrite <- rev_eq in CONT. repeat rewrite rev_app in CONT. ss.
      rewrite rev_unit in CONT. rewrite <- app_assoc in CONT. inv CONT.
      esplits. eauto.
    }
    des; subst.
    { rewrite snoc_eq_snoc in CONT. des. ss. }
    hexploit IHRTC; eauto. i. des.
    + left. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
    + right. esplits; eauto. econs 2; eauto; [| rewrite app_nil_l]; ss.
      econs; [| rewrite app_nil_r]; ss. econs 13. econs; eauto; ss.
      rewrite <- app_inv_tail_iff. rewrite <- app_assoc. eauto.
Qed.

