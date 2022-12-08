Require Import Ensembles.
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
    forall mid, (mmts |₁ (Complement _ mids)) mid = (thr_term.(Thread.mmts) |₁ (Complement _ mids)) mid>>
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
