Require Import Ensembles.
Require Import List.
Import ListNotations.

Require Import HahnList.
Require Import sflib.

From Memento Require Import Utils.
From Memento Require Import Syntax.
From Memento Require Import Semantics.
From Memento Require Import Common.

Set Implicit Arguments.

Lemma lift_cont:
  forall env tr thr thr_term c_base c,
    c_base = [] ->
    Thread.rtc env tr thr thr_term c_base ->
  Thread.rtc env tr
    (Thread.mk thr.(Thread.stmt) (thr.(Thread.cont) ++ c) thr.(Thread.ts) thr.(Thread.mmts))
    (Thread.mk thr_term.(Thread.stmt) (thr_term.(Thread.cont) ++ c) thr_term.(Thread.ts) thr_term.(Thread.mmts))
    c.
Proof.
  i. induction H0; subst.
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

Lemma relax_base:
  forall env tr thr thr_term c_base,
    Thread.rtc env tr thr thr_term c_base ->
  Thread.rtc env tr thr thr_term [].
Proof.
  i. induction H.
  { econs; eauto. }
  subst. inv ONE. econs 2; eauto. econs; eauto. rewrite app_nil_r. ss.
Qed.

Lemma lift_mmt:
  (* TODO: Define mid_pfx from ts.regs *)
  forall envt env labs s mid_pfx mids tr ts mmts thr_term,
    envt labs s ->
    mmt_id_exp mid_pfx labs = mids ->
    Thread.rtc env tr (Thread.mk s [] ts mmts) thr_term [] ->
  Thread.rtc env tr
    (Thread.mk s [] ts (mmts | mids))
    (Thread.mk thr_term.(Thread.stmt) thr_term.(Thread.cont) thr_term.(Thread.ts) (thr_term.(Thread.mmts) | mids))
    []
  /\ mmts | (Complement _ mids) = thr_term.(Thread.mmts) | (Complement _ mids)
  /\ exists mmts_a,
      Thread.rtc env tr
        (Thread.mk s [] ts ((mmts | mids) ⊎ (mmts_a | (Complement _ mids))))
        (Thread.mk thr_term.(Thread.stmt) thr_term.(Thread.cont) thr_term.(Thread.ts) ((thr_term.(Thread.mmts) | mids) ⊎ (mmts_a | (Complement _ mids))))
        [].
Proof.
  admit.
Qed.



(*
  TODO: Fix conclusion.
  Lemma unlift_not_loopcont :
  forall env tr thr thr_term c_base rmap r s mid c c_sfx,
    c_base = c :: c_sfx ->
    (c = Cont.chkptcont rmap r s mid \/ c = Cont.fncont rmap r s) ->
    Thread.rtc env tr thr thr_term c_base ->
  Thread.rtc env tr thr thr_term [].
Proof.
  i. induction H1; subst; [econs |]; ss.
  hexploit IHrtc; eauto. i. econs 2; eauto.
  inv ONE. inversion NORMAL_STEP; inv STEP; econs; eauto; ss.
  all: rewrite app_nil_r; eauto.
Qed. *)