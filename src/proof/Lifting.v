Require Import Ensembles.
Require Import EquivDec.
Require Import FunctionalExtensionality.
Require Import Lia.
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

Lemma snoc_split A:
  forall (c_pfx: list A) x c_loops y c2,
    c_pfx ++ [x] = c_loops ++ y :: c2 ->
  (c2 = [] /\ c_pfx = c_loops /\ x = y)
  \/ (exists c2', c2 = c2' ++ [x] /\ c_pfx = c_loops ++ y :: c2').
Proof.
  intros c_pfx x c_loops y c2 EQ. destruct c2 as [|z c2'] using rev_ind.
  - left. rewrite snoc_eq_snoc in EQ. des. subst. ss.
  - right. clear IHc2'. rewrite app_comm_cons, app_assoc in EQ.
    rewrite snoc_eq_snoc in EQ. des. subst. eauto.
Qed.

Lemma step_lift:
  forall env tr s c ts mmts s' c' ts' mmts' c_a,
    Thread.step env tr (Thread.mk s c ts mmts) (Thread.mk s' c' ts' mmts') ->
  Thread.step env tr (Thread.mk s (c ++ c_a) ts mmts) (Thread.mk s' (c' ++ c_a) ts' mmts').
Proof.
  intros env tr s c ts mmts s' c' ts' mmts' c_a STEP. inv STEP; try (econs; eauto; ss; fail).
  - eapply Thread.step_return; eauto. rewrite <- app_assoc. ss.
  - eapply Thread.step_chkpt_return; eauto. rewrite <- app_assoc. ss.
Qed.

Lemma step_lower:
  forall env tr s c c_b ts mmts thr' c',
    Thread.step env tr (Thread.mk s (c ++ c_b) ts mmts) thr' ->
    thr'.(Thread.cont) = c' ++ c_b ->
    (c = [] -> forall e s_rem, s <> stmt_continue e :: s_rem) ->
  Thread.step env tr (Thread.mk s c ts mmts) (Thread.mk thr'.(Thread.stmt) c' thr'.(Thread.ts) thr'.(Thread.mmts)).
Proof.
  intros env tr s c c_b ts mmts thr' c' STEP BASE NCONT.
  inv STEP; ss; try (apply app_inv_tail in BASE; subst; econs; eauto; fail).
  - rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst. econs; eauto.
  - apply app_inv_tail in BASE. subst.
    destruct c' as [|x c1]; ss.
    { exfalso. eapply NCONT; eauto. }
    inv CONT. econs; eauto.
  - destruct c as [|x c1]; ss.
    + exfalso. rewrite BASE in CONT. apply f_equal with (f := @length _) in CONT.
      simpl in CONT. rewrite app_length in CONT. lia.
    + injection CONT as X C1. subst. apply app_inv_tail in C1. subst. econs; eauto.
  - rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst. econs; eauto.
  - rewrite BASE, app_comm_cons, app_assoc in CONT. apply app_inv_tail in CONT. subst.
    eapply Thread.step_return; eauto.
  - rewrite app_comm_cons in BASE. apply app_inv_tail in BASE. subst. econs; eauto.
  - rewrite BASE, app_comm_cons, app_assoc in CONT. apply app_inv_tail in CONT. subst.
    eapply Thread.step_chkpt_return; eauto.
Qed.

(* Lemma H.5 *)
Lemma lift_cont:
  forall env tr s1 c1 ts1 mmts1 s2 c2 ts2 mmts2 c_a,
    Thread.rtc env [] tr (Thread.mk s1 c1 ts1 mmts1) (Thread.mk s2 c2 ts2 mmts2) ->
  Thread.rtc env c_a tr (Thread.mk s1 (c1 ++ c_a) ts1 mmts1) (Thread.mk s2 (c2 ++ c_a) ts2 mmts2).
Proof.
  intros env tr s1 c1 ts1 mmts1 s2 c2 ts2 mmts2 c_a RTC.
  remember (Thread.mk s1 c1 ts1 mmts1) as thr1 eqn:THR1.
  remember (Thread.mk s2 c2 ts2 mmts2) as thr2 eqn:THR2.
  revert s1 c1 ts1 mmts1 THR1. induction RTC; i; subst.
  { inv THR1. econs 1. }
  inv ONE. destruct thr0 as [s0 c0 ts0 mmts0]. ss. rewrite app_nil_r in BASE. subst.
  econs 2; [| eapply IHRTC; eauto | eauto].
  econs; [eapply step_lift; eauto | ss].
Qed.

Lemma rtc_relax_base_cont:
  forall env tr thr thr_term c_base c_pfx c_sfx,
    Thread.rtc env c_base tr thr thr_term ->
    c_base = c_pfx ++ c_sfx ->
  Thread.rtc env c_sfx tr thr thr_term.
Proof.
  i. subst. induction H.
  { econs; eauto. }
  subst. inv ONE. econs 2; eauto. econs; eauto. rewrite BASE. rewrite app_assoc. ss.
Qed.

Lemma rtc_lift_nil:
  forall env tr s c ts mmts s' c' ts' mmts' c_a,
    Thread.rtc env [] tr (Thread.mk s c ts mmts) (Thread.mk s' c' ts' mmts') ->
  Thread.rtc env [] tr (Thread.mk s (c ++ c_a) ts mmts) (Thread.mk s' (c' ++ c_a) ts' mmts').
Proof.
  intros env tr s c ts mmts s' c' ts' mmts' c_a RTC.
  eapply rtc_relax_base_cont; [eapply lift_cont; exact RTC | symmetry; apply app_nil_r].
Qed.

Inductive seq_rel (s_a: list Stmt) : list Stmt -> list Cont.t -> list Stmt -> list Cont.t -> Prop :=
| seq_rel_nil
    s
  : seq_rel s_a s [] (s ++ s_a) []
| seq_rel_cont
    s c_pfx c_base
  : seq_rel s_a s (c_pfx ++ [c_base]) s (c_pfx ++ [Cont.seq c_base s_a])
.

Lemma seq_rel_sc s_a s c s' c':
  seq_rel s_a s c s' c' <-> (s, c) ++₁ s_a = (s', c').
Proof.
  split; i.
  - inv H.
    + apply seq_sc_nil.
    + apply seq_sc_last.
  - destruct c as [|c_base c_pfx] using rev_ind.
    + rewrite seq_sc_nil in H. inv H. econs.
    + clear IHc_pfx. rewrite seq_sc_last in H. inv H. econs.
Qed.

Lemma step_seq_lift:
  forall env tr s c ts mmts s' c' ts' mmts' s_a S C,
    Thread.step env tr (Thread.mk s c ts mmts) (Thread.mk s' c' ts' mmts') ->
    seq_rel s_a s c S C ->
  exists S' C',
    seq_rel s_a s' c' S' C'
    /\ Thread.step env tr (Thread.mk S C ts mmts) (Thread.mk S' C' ts' mmts').
Proof.
  intros env tr s c ts mmts s' c' ts' mmts' s_a S C STEP REL.
  inv REL.
  - inv STEP; try (esplits; [econs | econs; eauto]; fail); ss.
    + esplits; [econs|]. rewrite <- app_assoc. econs; eauto.
    + esplits; [eapply (@seq_rel_cont s_a _ [])|]. econs; eauto.
    + esplits; [eapply (@seq_rel_cont s_a _ [])|]. econs; eauto.
    + destruct c_loops; ss.
    + esplits; [eapply (@seq_rel_cont s_a _ [])|]. econs; eauto.
    + destruct c_loops; ss.
  - inv STEP; try (esplits; [econs | econs; eauto]; fail).
    + esplits; [eapply (@seq_rel_cont s_a _ (_ :: _))|]. econs; eauto.
    + hexploit (@snoc_split _ _ _ [] _ _ CONT).
      intros [(C2 & C_PFX & C_BASE) | (c2' & C2 & C_PFX)]; subst; ss.
      * esplits; [eapply (@seq_rel_cont s_a _ [])|]. econs; eauto. ss.
      * esplits; [eapply (@seq_rel_cont s_a _ (_ :: _))|]. econs; eauto. ss.
    + hexploit (@snoc_split _ _ _ [] _ _ CONT).
      intros [(C2 & C_PFX & C_BASE) | (c2' & C2 & C_PFX)]; subst; ss.
      * esplits; [econs|]. econs; eauto.
      * esplits; [eapply seq_rel_cont|]. econs; eauto.
    + esplits; [eapply (@seq_rel_cont s_a _ (_ :: _))|]. econs; eauto.
    + hexploit snoc_split; eauto. intros [(C2 & C_PFX & C_BASE) | (c2' & C2 & C_PFX)]; subst.
      * esplits; [econs|]. eapply Thread.step_return; eauto.
      * esplits; [eapply seq_rel_cont|]. eapply Thread.step_return; eauto. rewrite <- app_assoc. ss.
    + esplits; [eapply (@seq_rel_cont s_a _ (_ :: _))|]. econs; eauto.
    + hexploit snoc_split; eauto. intros [(C2 & C_PFX & C_BASE) | (c2' & C2 & C_PFX)]; subst.
      * esplits; [econs|]. eapply Thread.step_chkpt_return; eauto.
      * esplits; [eapply seq_rel_cont|]. eapply Thread.step_chkpt_return; eauto. rewrite <- app_assoc. ss.
Qed.

Lemma seq_inv_loop c s_a rmap r s_body s_cont
      (SEQ: Cont.seq c s_a = Cont.loopcont rmap r s_body s_cont):
  exists s_cont0, c = Cont.loopcont rmap r s_body s_cont0 /\ s_cont = s_cont0 ++ s_a.
Proof. destruct c; inv SEQ. eauto. Qed.

Lemma seq_inv_fn c s_a rmap r s_cont
      (SEQ: Cont.seq c s_a = Cont.fncont rmap r s_cont):
  exists s_cont0, c = Cont.fncont rmap r s_cont0 /\ s_cont = s_cont0 ++ s_a.
Proof. destruct c; inv SEQ. eauto. Qed.

Lemma seq_inv_chkpt c s_a rmap r s_cont m
      (SEQ: Cont.seq c s_a = Cont.chkptcont rmap r s_cont m):
  exists s_cont0, c = Cont.chkptcont rmap r s_cont0 m /\ s_cont = s_cont0 ++ s_a.
Proof. destruct c; inv SEQ. eauto. Qed.

Lemma step_seq_unlift:
  forall env tr s c S C ts mmts thr' s_a,
    seq_rel s_a s c S C ->
    (s <> [] \/ c <> []) ->
    Thread.step env tr (Thread.mk S C ts mmts) thr' ->
  exists s' c',
    seq_rel s_a s' c' thr'.(Thread.stmt) thr'.(Thread.cont)
    /\ Thread.step env tr (Thread.mk s c ts mmts) (Thread.mk s' c' thr'.(Thread.ts) thr'.(Thread.mmts)).
Proof.
  intros env tr s c S C ts mmts thr' s_a REL NE STEP.
  inv REL.
  - destruct s as [|x s1]; [des; ss|]. ss.
    inv STEP; ss; try (esplits; [econs | econs; eauto]; fail).
    + esplits; [rewrite app_assoc; econs | econs; eauto].
    + esplits; [eapply (@seq_rel_cont s_a _ [] (Cont.loopcont _ _ _ _)) | econs; eauto].
    + esplits; [eapply (@seq_rel_cont s_a _ [] (Cont.fncont _ _ _)) | econs; eauto].
    + destruct c_loops; ss.
    + esplits; [eapply (@seq_rel_cont s_a _ [] (Cont.chkptcont _ _ _ _)) | econs; eauto].
    + destruct c_loops; ss.
  - inv STEP; ss; try (esplits; [econs | econs; eauto]; fail).
    + esplits; [eapply (@seq_rel_cont s_a _ (_ :: _)) | econs; eauto].
    + hexploit (@snoc_split _ _ _ [] _ _ CONT).
      intros [(C2 & C_PFX & C_BASE) | (c2' & C2 & C_PFX)]; subst; ss.
      * apply seq_inv_loop in C_BASE. destruct C_BASE as (s_cont0 & C_BASE & S_CONT). subst.
        esplits; [eapply (@seq_rel_cont s_a _ []) | econs; eauto; ss].
      * esplits; [eapply (@seq_rel_cont s_a _ (_ :: _)) | econs; eauto]. ss.
    + hexploit (@snoc_split _ _ _ [] _ _ CONT).
      intros [(C2 & C_PFX & C_BASE) | (c2' & C2 & C_PFX)]; subst; ss.
      * apply seq_inv_loop in C_BASE. destruct C_BASE as (s_cont0 & C_BASE & S_CONT). subst.
        esplits; [econs | econs; eauto; ss].
      * esplits; [eapply seq_rel_cont | econs; eauto; ss].
    + esplits; [eapply (@seq_rel_cont s_a _ (_ :: _)) | econs; eauto].
    + hexploit snoc_split; eauto. intros [(C2 & C_PFX & C_BASE) | (c2' & C2 & C_PFX)]; subst.
      * apply seq_inv_fn in C_BASE. destruct C_BASE as (s_cont0 & C_BASE & S_CONT). subst.
        esplits; [econs | eapply Thread.step_return; eauto].
      * esplits; [eapply seq_rel_cont | eapply Thread.step_return; eauto]. rewrite <- app_assoc. ss.
    + esplits; [eapply (@seq_rel_cont s_a _ (_ :: _)) | econs; eauto].
    + hexploit snoc_split; eauto. intros [(C2 & C_PFX & C_BASE) | (c2' & C2 & C_PFX)]; subst.
      * apply seq_inv_chkpt in C_BASE. destruct C_BASE as (s_cont0 & C_BASE & S_CONT). subst.
        esplits; [econs | eapply Thread.step_chkpt_return; eauto].
      * esplits; [eapply seq_rel_cont | eapply Thread.step_chkpt_return; eauto]. rewrite <- app_assoc. ss.
Qed.

(* Lemma H.4 *)
Lemma seq_lifting:
  forall env tr s1 c1 ts1 mmts1 s2 c2 ts2 mmts2 s,
    Thread.rtc env [] tr (Thread.mk s1 c1 ts1 mmts1) (Thread.mk s2 c2 ts2 mmts2) ->
  exists s_m1 s_m2 c_m1 c_m2,
    Thread.rtc env [] tr (Thread.mk s_m1 c_m1 ts1 mmts1) (Thread.mk s_m2 c_m2 ts2 mmts2)
    /\ (s_m1, c_m1) = (s1, c1) ++₁ s
    /\ (s_m2, c_m2) = (s2, c2) ++₁ s.
Proof.
  intros env tr s1 c1 ts1 mmts1 s2 c2 ts2 mmts2 s RTC.
  remember (Thread.mk s1 c1 ts1 mmts1) as thr1 eqn:THR1.
  remember (Thread.mk s2 c2 ts2 mmts2) as thr2 eqn:THR2.
  revert s1 c1 ts1 mmts1 THR1. induction RTC; i; subst.
  - inv THR1. destruct ((s1, c1) ++₁ s) as [S C] eqn:SC.
    esplits; [econs | eauto | eauto].
  - inv ONE. rewrite app_nil_r in BASE. subst.
    destruct thr0 as [s0 c0 ts0 mmts0].
    destruct ((s1, c1) ++₁ s) as [S C] eqn:SC. apply seq_rel_sc in SC.
    hexploit step_seq_lift; eauto. intros (S' & C' & REL' & STEP').
    hexploit IHRTC; eauto. intros (s_m1 & s_m2 & c_m1 & c_m2 & RTC' & SC1 & SC2).
    apply seq_rel_sc in REL'. rewrite REL' in SC1. inv SC1.
    esplits; [|eauto|eauto]. eapply rtc_nil_step; eauto.
Qed.

Lemma seq_cases_gen:
  forall env tr thr thr_term,
    Thread.rtc env [] tr thr thr_term ->
  forall s c s_r,
    seq_rel s_r s c thr.(Thread.stmt) thr.(Thread.cont) ->
    (s <> [] \/ c <> []) ->
  (exists s_m c_m,
      Thread.rtc env [] tr (Thread.mk s c thr.(Thread.ts) thr.(Thread.mmts))
        (Thread.mk s_m c_m thr_term.(Thread.ts) thr_term.(Thread.mmts))
      /\ seq_rel s_r s_m c_m thr_term.(Thread.stmt) thr_term.(Thread.cont)
      /\ (s_m <> [] \/ c_m <> []))
  \/ (exists tr1 tr2 ts1 mmts1,
      tr = tr1 ++ tr2
      /\ Thread.rtc env [] tr1 (Thread.mk s c thr.(Thread.ts) thr.(Thread.mmts)) (Thread.mk [] [] ts1 mmts1)
      /\ Thread.rtc env [] tr2 (Thread.mk s_r [] ts1 mmts1) thr_term).
Proof.
  intros env tr thr thr_term RTC. induction RTC; intros s c s_r REL NE.
  - left. esplits; [econs | eauto | eauto].
  - subst. inv ONE. rewrite app_nil_r in BASE. subst.
    destruct thr as [S C ts mmts]. ss.
    hexploit step_seq_unlift; eauto. intros (s' & c' & REL' & STEP').
    destruct (classic (s' = [] /\ c' = [])) as [[S' C'] | NE'].
    + subst. inv REL'.
      * right. destruct thr0 as [s0 c0 ts0 mmts0]. ss. subst.
        esplits; [| eapply rtc_one; eauto | eauto]. ss.
      * destruct c_pfx; ss.
    + hexploit IHRTC; eauto.
      { destruct s' as [|x s'']; [destruct c' as [|y c'']; [exfalso; apply NE'; split; ss | right; ss] | left; ss]. }
      intros [(s_m & c_m & RTC' & REL_M & NE_M) | (tr1' & tr2' & ts1 & mmts1 & TR & RTC1 & RTC2)].
      * left. esplits; [eapply rtc_nil_step; eauto | eauto | eauto].
      * right. subst. esplits; [| eapply rtc_nil_step; eauto | eauto]. rewrite app_assoc. ss.
Qed.

(* Lemma H.8 *)
Lemma seq_cases:
  forall env tr s_l s_r ts mmts s_w c_w ts_w mmts_w,
    Thread.rtc env [] tr (Thread.mk (s_l ++ s_r) [] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  (exists s_m c_m,
      Thread.rtc env [] tr (Thread.mk s_l [] ts mmts) (Thread.mk s_m c_m ts_w mmts_w)
      /\ (s_w, c_w) = (s_m, c_m) ++₁ s_r
      /\ (s_m, c_m) <> ([], []))
  \/ (exists tr1 tr2 ts1 mmts1,
      tr = tr1 ++ tr2
      /\ Thread.rtc env [] tr1 (Thread.mk s_l [] ts mmts) (Thread.mk [] [] ts1 mmts1)
      /\ Thread.rtc env [] tr2 (Thread.mk s_r [] ts1 mmts1) (Thread.mk s_w c_w ts_w mmts_w)).
Proof.
  intros env tr s_l s_r ts mmts s_w c_w ts_w mmts_w RTC.
  destruct s_l as [|x s_l].
  { right. esplits; [| econs | eauto]. ss. }
  hexploit seq_cases_gen; eauto.
  { econs. }
  { left. ss. }
  intros [(s_m & c_m & RTC' & REL & NE) | (tr1 & tr2 & ts1 & mmts1 & TR & RTC1 & RTC2)]; ss.
  - left. apply seq_rel_sc in REL. esplits; eauto. ii. inv H. des; ss.
  - right. esplits; eauto.
Qed.

Lemma step_cont_cases:
  forall env tr s c ts mmts thr',
    Thread.step env tr (Thread.mk s c ts mmts) thr' ->
  (exists c0, thr'.(Thread.cont) = c0 ++ c)
  \/ (exists x s_rem, c = x :: thr'.(Thread.cont) /\ Cont.is_loop x = true /\ s = stmt_break :: s_rem)
  \/ (exists e s_rem c_loops x,
        s = stmt_return e :: s_rem /\ c = c_loops ++ x :: thr'.(Thread.cont)
        /\ Cont.Loops c_loops /\ ~ Cont.Loops [x]).
Proof.
  intros env tr s c ts mmts thr' STEP.
  inv STEP; ss; try (left; exists []; ss; fail); try (left; eexists [_]; ss; fail).
  - right. left. esplits; eauto.
  - right. right. esplits; eauto. intro L. inv L. ss.
  - right. right. esplits; eauto. intro L. inv L. ss.
Qed.

Lemma frame_split:
  forall c_loops c c' c_base x c_rest,
    c ++ c' :: c_base = c_loops ++ x :: c_rest ->
    Cont.Loops c_loops ->
    ~ Cont.Loops [x] ->
  (exists c1, c = c_loops ++ x :: c1 /\ c_rest = c1 ++ c' :: c_base)
  \/ (Cont.Loops (c ++ [c']) /\ exists c2, c_base = c2 ++ x :: c_rest)
  \/ (c = c_loops /\ x = c' /\ c_rest = c_base).
Proof.
  induction c_loops as [|z zs IH]; intros c c' c_base x c_rest EQ LOOPS NLOOP.
  - destruct c as [|y c1]; ss.
    + inv EQ. right. right. ss.
    + inv EQ. left. eauto.
  - inversion LOOPS as [|? ? Z ZS]. subst. destruct c as [|y c1]; ss.
    + inv EQ. right. left. split.
      * econs; [ss|econs].
      * eauto.
    + inv EQ. hexploit IH; eauto. intros [(c2 & C1 & REST) | [(L & c2 & C_BASE) | (C1 & X & REST)]]; subst.
      * left. eauto.
      * right. left. split; eauto. econs; ss.
      * right. right. ss.
Qed.

Lemma app_suffix_absurd A:
  forall (l c2: list A) x pfx,
    l = pfx ++ c2 ++ x :: l ->
  False.
Proof.
  i. apply f_equal with (f := @length _) in H. rewrite ! app_length in H. ss. lia.
Qed.

Lemma chkpt_fn_cases:
  forall env c_b tr thr thr_term c c' c_base,
    Thread.rtc env c_b tr thr thr_term ->
    thr.(Thread.cont) = c ++ c' :: c_base ->
    ~ Cont.Loops [c'] ->
  (exists c_pfx,
      thr_term.(Thread.cont) = c_pfx ++ c' :: c_base
      /\ Thread.rtc env [] tr
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts)))
  \/ (exists tr0 tr1 s_r c_r ts_r mmts_r e,
      tr = tr0 ++ tr1
      /\ Thread.rtc env [] tr0
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk (stmt_return e :: s_r) c_r ts_r mmts_r)
      /\ Thread.tc env c_b tr1 (Thread.mk (stmt_return e :: s_r) (c_r ++ c' :: c_base) ts_r mmts_r) thr_term
      /\ Cont.Loops c_r).
Proof.
  intros env c_b tr thr thr_term c c' c_base RTC. revert c.
  induction RTC; intros c0 CONT NLOOP.
  { left. esplits; eauto. econs 1. }
  subst. inversion ONE as [c_p STEP BASE].
  destruct thr as [s1 k1 ts1 mmts1], thr0 as [s2 k2 ts2 mmts2]. ss. subst k1.
  assert (LOWER: forall c1,
             k2 = c1 ++ c' :: c_base ->
             Thread.step env tr0 (Thread.mk s1 c0 ts1 mmts1) (Thread.mk s2 c1 ts2 mmts2)).
  { intros c1 CONT1.
    hexploit (@step_lower env tr0 s1 c0 (c' :: c_base) ts1 mmts1 (Thread.mk s2 k2 ts2 mmts2) c1); eauto.
    intros C0 e s_rem S1. subst c0 s1.
    destruct (step_continue_inv STEP) as [_ (v & rmap & r & s_body & s_cont & c'' & _ & CONT_EQ & _)].
    inv CONT_EQ. apply NLOOP. econs; [ss | econs]. }
  assert (CONT_IH: forall c1,
             k2 = c1 ++ c' :: c_base ->
             (exists c_pfx,
                 thr_term.(Thread.cont) = c_pfx ++ c' :: c_base
                 /\ Thread.rtc env [] (tr0 ++ tr1) (Thread.mk s1 c0 ts1 mmts1)
                      (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts)))
             \/ (exists tr2 tr3 s_r c_r ts_r mmts_r e,
                 tr0 ++ tr1 = tr2 ++ tr3
                 /\ Thread.rtc env [] tr2 (Thread.mk s1 c0 ts1 mmts1) (Thread.mk (stmt_return e :: s_r) c_r ts_r mmts_r)
                 /\ Thread.tc env c_b tr3 (Thread.mk (stmt_return e :: s_r) (c_r ++ c' :: c_base) ts_r mmts_r) thr_term
                 /\ Cont.Loops c_r)).
  { intros c1 CONT1. hexploit IHRTC; eauto.
    intros [(c_pfx & CONT_T & RTC') | (tr2 & tr3 & s_r & c_r & ts_r & mmts_r & e & TR & RTC0 & TC & LOOPS)].
    - left. esplits; eauto. eapply rtc_nil_step; eauto.
    - right. subst. esplits; [| eapply rtc_nil_step; eauto | eauto | eauto]. rewrite app_assoc. ss.
  }
  hexploit step_cont_cases; eauto. ss.
  intros [(c1 & CONT1) | [(x & s_rem & CONT1 & LOOP & S1) | (e & s_rem & c_loops & x & S1 & CONT1 & LOOPS & NLOOP_X)]].
  - apply (CONT_IH (c1 ++ c0)). rewrite CONT1, app_assoc. ss.
  - destruct c0 as [|y c1]; ss.
    + inv CONT1. exfalso. apply NLOOP. econs; [ss|econs].
    + injection CONT1 as Y C1. apply (CONT_IH c1). symmetry. exact C1.
  - hexploit frame_split; eauto.
    intros [(c1 & C0 & REST) | [(L & c2 & C_BASE) | (C0 & X & REST)]].
    + apply (CONT_IH c1). exact REST.
    + exfalso. apply NLOOP. apply Cont.loops_app_distr in L. destruct L as [_ L]. exact L.
    + subst. right. esplits; [| econs 1 | econs; eauto | eauto]; ss.
Qed.

Lemma loop_cases:
  forall env c_base tr thr thr_term c rmap r s_body s_cont,
    Thread.rtc env c_base tr thr thr_term ->
    thr.(Thread.cont) = c ++ Cont.loopcont rmap r s_body s_cont :: c_base ->
  Thread.rtc env (Cont.loopcont rmap r s_body s_cont :: c_base) tr thr thr_term
  \/ (exists tr0 tr1 s_r ts_r mmts_r,
      tr = tr0 ++ tr1
      /\ Thread.rtc env (Cont.loopcont rmap r s_body s_cont :: c_base) tr0 thr
           (Thread.mk (stmt_break :: s_r) (Cont.loopcont rmap r s_body s_cont :: c_base) ts_r mmts_r)
      /\ Thread.rtc env c_base tr1
           (Thread.mk s_cont c_base (TState.mk rmap ts_r.(TState.time)) mmts_r) thr_term).
Proof.
  intros env c_base tr thr thr_term c rmap r s_body s_cont RTC. revert c.
  induction RTC; intros c0 CONT.
  { left. econs 1. }
  subst. inversion ONE as [c_p STEP BASE].
  destruct thr as [s1 k1 ts1 mmts1]. ss. subst k1.
  assert (CONT_IH: forall c1,
             thr0.(Thread.cont) = c1 ++ Cont.loopcont rmap r s_body s_cont :: c_base ->
             Thread.rtc env (Cont.loopcont rmap r s_body s_cont :: c_base) (tr0 ++ tr1)
               (Thread.mk s1 (c0 ++ Cont.loopcont rmap r s_body s_cont :: c_base) ts1 mmts1) thr_term
             \/ (exists tr2 tr3 s_r ts_r mmts_r,
                 tr0 ++ tr1 = tr2 ++ tr3
                 /\ Thread.rtc env (Cont.loopcont rmap r s_body s_cont :: c_base) tr2
                      (Thread.mk s1 (c0 ++ Cont.loopcont rmap r s_body s_cont :: c_base) ts1 mmts1)
                      (Thread.mk (stmt_break :: s_r) (Cont.loopcont rmap r s_body s_cont :: c_base) ts_r mmts_r)
                 /\ Thread.rtc env c_base tr3
                      (Thread.mk s_cont c_base (TState.mk rmap ts_r.(TState.time)) mmts_r) thr_term)).
  { intros c1 CONT1. hexploit IHRTC; eauto.
    intros [ONG | (tr2 & tr3 & s_r & ts_r & mmts_r & TR & BRK & OUT)].
    - left. eapply rtc_step; eauto.
    - right. subst. esplits; [| eapply rtc_step; eauto | eauto]. rewrite app_assoc. ss.
  }
  hexploit step_cont_cases; eauto.
  intros [(c1 & CONT1) | [(x & s_rem & CONT1 & LOOP & S1) | (e & s_rem & c_loops & x & S1 & CONT1 & LOOPS & NLOOP_X)]].
  - apply (CONT_IH (c1 ++ c0)). rewrite CONT1, app_assoc. ss.
  - destruct c0 as [|y c1]; ss.
    + injection CONT1 as X K2. subst x s1.
      destruct (step_break_inv STEP) as [TR0 (rmap' & r' & s_body' & s_cont' & c'' & CONT_EQ & THR0)].
      injection CONT_EQ as RMAP R SB SC C''. subst rmap' r' s_body' s_cont' c'' thr0 tr0.
      right. exists [], tr1. esplits; [ss | econs 1 | exact RTC].
    + injection CONT1 as Y C1. apply (CONT_IH c1). symmetry. exact C1.
  - hexploit frame_split; eauto.
    intros [(c1 & C0 & REST) | [(L & c2 & C_BASE) | (C0 & X & REST)]].
    + apply (CONT_IH c1). exact REST.
    + exfalso. rewrite C_BASE in BASE. eapply app_suffix_absurd. eauto.
    + exfalso. subst. apply NLOOP_X. econs; [ss|econs].
Qed.

Lemma first_loop_iter:
  forall env tr thr thr_term c rmap r s,
    Thread.rtc env [Cont.loopcont rmap r s []] tr thr thr_term ->
    thr.(Thread.cont) = c ++ [Cont.loopcont rmap r s []] ->
  (exists c_pfx,
      thr_term.(Thread.cont) = c_pfx ++ [Cont.loopcont rmap r s []]
      /\ Thread.rtc env [] tr
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk thr_term.(Thread.stmt) c_pfx thr_term.(Thread.ts) thr_term.(Thread.mmts)))
  \/ (exists tr1 tr2 e s1 ts1 mmts1,
      tr = tr1 ++ tr2
      /\ Thread.rtc env [] tr1
          (Thread.mk thr.(Thread.stmt) c thr.(Thread.ts) thr.(Thread.mmts))
          (Thread.mk (stmt_continue e :: s1) [] ts1 mmts1)
      /\ Thread.rtc env [Cont.loopcont rmap r s []] tr2
          (Thread.mk (stmt_continue e :: s1) [Cont.loopcont rmap r s []] ts1 mmts1)
          thr_term).
Proof.
  intros env tr thr thr_term c rmap r s RTC. revert c.
  induction RTC; intros c0 CONT.
  { left. esplits; eauto. econs 1. }
  subst. inversion ONE as [c_p STEP BASE].
  destruct thr as [s1 k1 ts1 mmts1], thr0 as [s2 k2 ts2 mmts2]. ss. subst k1.
  destruct (classic (c0 = [] /\ exists e s_rem, s1 = stmt_continue e :: s_rem)) as [(C0 & e & s_rem & S1) | NCONT].
  { subst. right. exists [], (tr0 ++ tr1). esplits; [ss | econs 1 | econs 2; eauto]. }
  hexploit (@step_lower env tr0 s1 c0 [Cont.loopcont rmap r s []] ts1 mmts1 (Thread.mk s2 k2 ts2 mmts2) c_p); eauto.
  { intros C0 e s_rem S1. apply NCONT. eauto. }
  ss. intro LOWER.
  hexploit IHRTC; eauto.
  intros [(c_pfx & CONT_T & RTC') | (tr2 & tr3 & e & s3 & ts3 & mmts3 & TR & RTC2 & RTC3)].
  - left. esplits; eauto. eapply rtc_nil_step; eauto.
  - right. subst. esplits; [| eapply rtc_nil_step; eauto | eauto]. rewrite app_assoc. ss.
Qed.

Lemma last_loop_iter:
  forall env tr thr thr_term c_pfx rmap r s,
    Thread.rtc env [Cont.loopcont rmap r s []] tr thr thr_term ->
    thr.(Thread.cont) = c_pfx ++ [Cont.loopcont rmap r s []] ->
  exists tr1 tr2 s1 c1 ts1 mmts1 c_pfx_term,
    tr = tr1 ++ tr2
    /\ ((s1 = thr.(Thread.stmt) /\ c1 = c_pfx /\ ts1 = thr.(Thread.ts) /\ mmts1 = thr.(Thread.mmts) /\ tr1 = [])
        \/ (exists e s_r ts_r v,
              Thread.rtc env [Cont.loopcont rmap r s []] tr1 thr
                (Thread.mk (stmt_continue e :: s_r) [Cont.loopcont rmap r s []] ts_r mmts1)
              /\ sem_expr ts_r.(TState.regs) e = Some v
              /\ s1 = s /\ c1 = []
              /\ ts1 = TState.mk (set_opt r v rmap) ts_r.(TState.time)))
    /\ thr_term.(Thread.cont) = c_pfx_term ++ [Cont.loopcont rmap r s []]
    /\ Thread.rtc env [] tr2
         (Thread.mk s1 c1 ts1 mmts1)
         (Thread.mk thr_term.(Thread.stmt) c_pfx_term thr_term.(Thread.ts) thr_term.(Thread.mmts)).
Proof.
  intros env tr thr thr_term c_pfx rmap r s RTC. revert c_pfx.
  induction RTC; intros c0 CONT.
  { exists [], [], thr.(Thread.stmt), c0, thr.(Thread.ts), thr.(Thread.mmts), c0.
    splits; [ss | left; splits; ss | exact CONT | econs 1]. }
  subst. inversion ONE as [c_p STEP BASE].
  destruct thr as [s1 k1 ts1 mmts1]. ss. subst k1.
  destruct (classic (c0 = [] /\ exists e s_rem, s1 = stmt_continue e :: s_rem)) as [(C0 & e & s_rem & S1) | NCONT].
  - subst c0 s1.
    destruct (step_continue_inv STEP) as [TR0 (v & rmap' & r' & s_body' & s_cont' & c'' & EVAL & CONT_EQ & THR0)].
    injection CONT_EQ as RMAP R SB SC C''. subst rmap' r' s_body' s_cont' c'' thr0 tr0.
    hexploit (IHRTC []); [ss|].
    intros (tr2 & tr3 & s3 & c3 & ts3 & mmts3 & c_pfx_term & TR & LAST & CONT_T & RTC').
    destruct LAST as [(S3 & C3 & TS3 & MMTS3 & TR2) | (e' & s_r & ts_r & v' & RTC_C & EVAL' & S3 & C3 & TS3)].
    + subst s3 c3 ts3 mmts3 tr2 tr1.
      exists [], tr3, s, [], (TState.mk (set_opt r v rmap) (TState.time ts1)), mmts1, c_pfx_term.
      splits; [ss | | exact CONT_T | exact RTC'].
      right. exists e, s_rem, ts1, v. splits; [econs 1 | exact EVAL | ss | ss | ss].
    + subst tr1 s3 c3 ts3.
      exists ([] ++ tr2), tr3, s, [], (TState.mk (set_opt r v' rmap) (TState.time ts_r)), mmts3, c_pfx_term.
      splits; [ss | | exact CONT_T | exact RTC'].
      right. exists e', s_r, ts_r, v'. splits; [| exact EVAL' | ss | ss | ss].
      eapply rtc_step; [exact STEP | exact BASE | exact RTC_C | ss].
  - hexploit (@step_lower env tr0 s1 c0 [Cont.loopcont rmap r s []] ts1 mmts1 thr0 c_p); eauto.
    { intros C0 e s_rem S1. apply NCONT. eauto. }
    intro LOWER.
    hexploit (IHRTC c_p); eauto.
    intros (tr2 & tr3 & s3 & c3 & ts3 & mmts3 & c_pfx_term & TR & LAST & CONT_T & RTC').
    destruct LAST as [(S3 & C3 & TS3 & MMTS3 & TR2) | (e' & s_r & ts_r & v' & RTC_C & EVAL' & S3 & C3 & TS3)].
    + subst tr1 tr2 s3 c3 ts3 mmts3.
      exists [], (tr0 ++ tr3), s1, c0, ts1, mmts1, c_pfx_term.
      splits; [ss | left; splits; ss | exact CONT_T |].
      eapply rtc_nil_step; [exact LOWER | exact RTC' | ss].
    + subst tr1 s3 c3 ts3.
      exists (tr0 ++ tr2), tr3, s, [], (TState.mk (set_opt r v' rmap) (TState.time ts_r)), mmts3, c_pfx_term.
      splits; [rewrite app_assoc; ss | | exact CONT_T | exact RTC'].
      right. exists e', s_r, ts_r, v'. splits; [| exact EVAL' | ss | ss | ss].
      eapply rtc_step; [exact STEP | exact BASE | exact RTC_C | ss].
Qed.

(* Lemma H.10 *)
Lemma loop_cases_H10:
  forall env tr s ts mmts s_w c_w ts_w mmts_w rmap r,
    Thread.rtc env [] tr (Thread.mk s [Cont.loopcont rmap r s []] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  Thread.rtc env [Cont.loopcont rmap r s []] tr
    (Thread.mk s [Cont.loopcont rmap r s []] ts mmts) (Thread.mk s_w c_w ts_w mmts_w)
  \/ (exists s_r ts_r,
        Thread.rtc env [Cont.loopcont rmap r s []] tr
          (Thread.mk s [Cont.loopcont rmap r s []] ts mmts)
          (Thread.mk (stmt_break :: s_r) [Cont.loopcont rmap r s []] ts_r mmts_w)
        /\ s_w = [] /\ c_w = [] /\ ts_w = TState.mk rmap ts_r.(TState.time)).
Proof.
  intros env tr s ts mmts s_w c_w ts_w mmts_w rmap r RTC.
  hexploit (@loop_cases env [] tr _ _ [] rmap r s [] RTC); [reflexivity |].
  intros [ONG | (tr0 & tr1 & s_r & ts_r & mmts_r & TR & BRK & OUT)]; [left; ss|].
  hexploit stop_means_no_step; [|exact OUT|]; [left; ss|]. intros [THR TR1].
  injection THR as <- <- <- <-. subst. rewrite app_nil_r. right. esplits; eauto.
Qed.

(* Lemma H.11 *)
Lemma first_loop_iter_H11:
  forall env tr s ts mmts s_w c_w ts_w mmts_w rmap r,
    Thread.rtc env [Cont.loopcont rmap r s []] tr
      (Thread.mk s [Cont.loopcont rmap r s []] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  (exists c_pfx,
      c_w = c_pfx ++ [Cont.loopcont rmap r s []]
      /\ Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk s_w c_pfx ts_w mmts_w))
  \/ (exists s1 ts1 mmts1 tr1 tr2 e,
        tr = tr1 ++ tr2
        /\ Thread.rtc env [] tr1 (Thread.mk s [] ts mmts) (Thread.mk (stmt_continue e :: s1) [] ts1 mmts1)
        /\ Thread.rtc env [Cont.loopcont rmap r s []] tr2
             (Thread.mk (stmt_continue e :: s1) [Cont.loopcont rmap r s []] ts1 mmts1)
             (Thread.mk s_w c_w ts_w mmts_w)).
Proof.
  intros env tr s ts mmts s_w c_w ts_w mmts_w rmap r RTC.
  hexploit (@first_loop_iter env tr _ _ [] rmap r s RTC); [reflexivity |].
  intros [(c_pfx & CONT & FST) | (tr1 & tr2 & e & s1 & ts1 & mmts1 & TR & FST & REST)]; ss.
  - left. eauto.
  - right. esplits; eauto.
Qed.

(* Lemma H.12 *)
Lemma last_loop_iter_H12:
  forall env tr s ts mmts s_w c_w ts_w mmts_w rmap r,
    Thread.rtc env [Cont.loopcont rmap r s []] tr
      (Thread.mk s [Cont.loopcont rmap r s []] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  exists ts1 mmts1 c_pfx tr1 tr2,
    tr = tr1 ++ tr2
    /\ ((ts1 = ts /\ mmts1 = mmts /\ tr1 = [])
        \/ (exists e s_r ts_r v,
              Thread.rtc env [Cont.loopcont rmap r s []] tr1
                (Thread.mk s [Cont.loopcont rmap r s []] ts mmts)
                (Thread.mk (stmt_continue e :: s_r) [Cont.loopcont rmap r s []] ts_r mmts1)
              /\ sem_expr ts_r.(TState.regs) e = Some v
              /\ ts1 = TState.mk (set_opt r v rmap) ts_r.(TState.time)))
    /\ c_w = c_pfx ++ [Cont.loopcont rmap r s []]
    /\ Thread.rtc env [] tr2 (Thread.mk s [] ts1 mmts1) (Thread.mk s_w c_pfx ts_w mmts_w).
Proof.
  intros env tr s ts mmts s_w c_w ts_w mmts_w rmap r RTC.
  hexploit (@last_loop_iter env tr _ _ [] rmap r s RTC); [reflexivity |].
  intros (tr1 & tr2 & s1 & c1 & ts1 & mmts1 & c_pfx & TR & LAST & CONT & ITER).
  destruct LAST as [(S1 & C1 & TS1 & MMTS1 & TR1) | (e & s_r & ts_r & v & ITERS & EVAL & S1 & C1 & TS1)];
    ss; subst.
  - exists ts, mmts, c_pfx, [], tr2. splits; ss. left. ss.
  - exists (TState.mk (set_opt r v rmap) (TState.time ts_r)), mmts1, c_pfx, tr1, tr2. splits; ss.
    right. esplits; eauto.
Qed.

(* Lemma H.13 *)
Lemma chkpt_fn_cases_H13:
  forall env tr s ts mmts s_w c_w ts_w mmts_w c_hd,
    ((exists rmap r m, c_hd = Cont.chkptcont rmap r [] m) \/ (exists rmap r, c_hd = Cont.fncont rmap r [])) ->
    Thread.rtc env [] tr (Thread.mk s [c_hd] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  (exists c_pfx,
      c_w = c_pfx ++ [c_hd]
      /\ Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk s_w c_pfx ts_w mmts_w))
  \/ (exists s_r c_r ts_r mmts_r e,
        Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk (stmt_return e :: s_r) c_r ts_r mmts_r)
        /\ Thread.step env [] (Thread.mk (stmt_return e :: s_r) (c_r ++ [c_hd]) ts_r mmts_r)
             (Thread.mk s_w c_w ts_w mmts_w)
        /\ s_w = [] /\ c_w = []).
Proof.
  intros env tr s ts mmts s_w c_w ts_w mmts_w c_hd HD RTC.
  assert (NLOOP: ~ Cont.Loops [c_hd]).
  { intro L. inv L. destruct HD as [(rmap & r & m & HD) | (rmap & r & HD)]; subst; ss. }
  hexploit (@chkpt_fn_cases env [] tr _ _ [] c_hd [] RTC); [reflexivity | exact NLOOP |].
  intros [(c_pfx & CONT & BODY) | (tr0 & tr1 & s_r & c_r & ts_r & mmts_r & e & TR & BODY & RET & LOOPS)]; ss.
  - left. eauto.
  - right. destruct (tc_nil_inv RET) as (tr2 & tr3 & thr2 & TR1 & STEP & REST).
    hexploit step_return_inv; [exact STEP | exact LOOPS | exact NLOOP |]. intros [TR2 (v & EVAL & THR2)].
    assert (DONE: thr2.(Thread.stmt) = [] /\ thr2.(Thread.cont) = []).
    { destruct HD as [(rmap & r & m & HD) | (rmap & r & HD)]; subst; ss; des; subst; ss. }
    destruct DONE as [S2 C2].
    hexploit stop_means_no_step; [left; split; eauto | exact REST |]. intros [THR TR3]. subst.
    rewrite ! app_nil_r. esplits; eauto.
Qed.

Definition ro_cont (envt: EnvType.t) (c: Cont.t) : Prop :=
  match c with
  | Cont.loopcont _ _ s_body s_cont => EnvType.ro_judge envt s_body /\ EnvType.ro_judge envt s_cont
  | Cont.fncont _ _ s_cont => EnvType.ro_judge envt s_cont
  | Cont.chkptcont _ _ _ _ => False
  end.

Definition ro_thread (envt: EnvType.t) (thr: Thread.t) : Prop :=
  EnvType.ro_judge envt thr.(Thread.stmt) /\ Forall (ro_cont envt) thr.(Thread.cont).

Lemma ro_judge_cons envt x s:
  EnvType.ro_judge envt (x :: s) <-> EnvType.ro_judge envt [x] /\ EnvType.ro_judge envt s.
Proof.
  rewrite ! EnvShape.ro_judge_forall. split.
  - intro FA. inv FA. split; [econs; [ss | econs] | ss].
  - intros [FA1 FA2]. inv FA1. econs; ss.
Qed.

Lemma ro_judge_app envt s1 s2:
  EnvType.ro_judge envt (s1 ++ s2) <-> EnvType.ro_judge envt s1 /\ EnvType.ro_judge envt s2.
Proof. rewrite ! EnvShape.ro_judge_forall. apply Forall_app. Qed.

Lemma ro_step:
  forall env envt tr thr1 thr2,
    TypeSystem.env_ok env envt ->
    ro_thread envt thr1 ->
    Thread.step env tr thr1 thr2 ->
  ro_thread envt thr2 /\ [] ~ tr /\ thr2.(Thread.mmts) = thr1.(Thread.mmts)
  /\ thr2.(Thread.ts).(TState.time) = thr1.(Thread.ts).(TState.time).
Proof.
  intros env envt tr thr1 thr2 [OK_RO OK_RW] [RO RO_C] STEP. unfold ro_thread.
  assert (NIL: [] ~ []) by apply trace_refine_eq.
  assert (READ: forall l v, [] ~ [Event.R l v]).
  { i. eapply refine_read; [apply trace_refine_eq | ss]. }
  inv STEP; ss; apply ro_judge_cons in RO; destruct RO as [ONE RO]; apply EnvShape.ro_judge_single in ONE; ss;
    try (splits; ss; fail).
  - destruct ONE as [RO_T RO_F]. splits; ss. apply ro_judge_app. split; ss. destruct b; ss.
  - splits; ss. econs; ss.
  - inversion RO_C as [|? ? FR RO_C']. subst. destruct FR as [RO_B RO_S]. splits; ss.
  - inversion RO_C as [|? ? FR RO_C']. subst. destruct FR as [RO_B RO_S]. splits; ss.
  - hexploit OK_RO; eauto. intros (prms' & s_f' & FIND' & RO_F & _). rewrite FIND in FIND'. inv FIND'.
    splits; ss. econs; ss.
  - apply Forall_app in RO_C. destruct RO_C as [_ RO_C]. inversion RO_C as [|? ? FR RO_C']. subst. splits; ss.
  - apply Forall_app in RO_C. destruct RO_C as [_ RO_C]. inversion RO_C as [|? ? FR RO_C']. subst. ss.
Qed.

Lemma ro_rtc:
  forall env envt c tr thr thr_term,
    TypeSystem.env_ok env envt ->
    Thread.rtc env c tr thr thr_term ->
    ro_thread envt thr ->
  ro_thread envt thr_term /\ [] ~ tr /\ thr_term.(Thread.mmts) = thr.(Thread.mmts)
  /\ thr_term.(Thread.ts).(TState.time) = thr.(Thread.ts).(TState.time).
Proof.
  intros env envt c tr thr thr_term OK RTC. induction RTC; i.
  - splits; ss. apply trace_refine_eq.
  - subst. inv ONE. hexploit ro_step; eauto. intros (RO0 & SILENT0 & MMTS0 & TIME0).
    hexploit IHRTC; eauto. intros (RO1 & SILENT1 & MMTS1 & TIME1).
    splits; ss.
    + rewrite <- (app_nil_l []). apply trace_refine_app; ss.
    + congr.
    + congr.
Qed.

Lemma ro_run:
  forall env envt s tr ts mmts s_w c_w ts_w mmts_w,
    TypeSystem.env_ok env envt ->
    EnvType.ro_judge envt s ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  [] ~ tr /\ mmts = mmts_w /\ ts.(TState.time) = ts_w.(TState.time).
Proof.
  i. hexploit ro_rtc; eauto.
  { split; ss. }
  intros (_ & SILENT & MMTS & TIME). ss.
Qed.

(* Lemma H.25 *)
Lemma read_only_statements:
  forall env envt s tr ts mmts s_w c_w ts_w mmts_w,
    TypeSystem.judge env envt ->
    EnvType.ro_judge envt s ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  [] ~ tr /\ mmts = mmts_w.
Proof.
  i. hexploit ro_run; eauto using TypeSystem.judge_env_ok. intros (SILENT & MMTS & _). ss.
Qed.

Definition rw_stmts (envt: EnvType.t) (labs: Ensemble Label) (s: list Stmt) : Prop :=
  Forall (fun x => exists labs', Included _ labs' labs /\ EnvType.rw_judge envt labs' [x]) s.

Definition styped (envt: EnvType.t) (labs: Ensemble Label) (s: list Stmt) : Prop :=
  rw_stmts envt labs s \/ EnvType.ro_judge envt s.

Definition bnd (envt: EnvType.t) (mids: Ensemble (list Label)) (rmap: VRegMap.t) (s: list Stmt) : Prop :=
  exists labs,
    styped envt labs s
    /\ forall pfx, rmap mid = Some (Val.mid pfx) -> Included _ (mmt_id_exp pfx labs) mids.

Definition frame_inv (envt: EnvType.t) (mids: Ensemble (list Label)) (c: Cont.t) : Prop :=
  match c with
  | Cont.loopcont rmap r s_body s_cont =>
      (forall v, bnd envt mids (set_opt r v rmap) s_body) /\ bnd envt mids rmap s_cont
  | Cont.fncont rmap r s_cont =>
      forall v, bnd envt mids (VRegMap.add r v rmap) s_cont
  | Cont.chkptcont rmap r s_cont m =>
      Ensembles.In _ mids m /\ forall v, bnd envt mids (VRegMap.add r v rmap) s_cont
  end.

Definition thr_inv (envt: EnvType.t) (mids: Ensemble (list Label)) (thr: Thread.t) : Prop :=
  bnd envt mids thr.(Thread.ts).(TState.regs) thr.(Thread.stmt)
  /\ Forall (frame_inv envt mids) thr.(Thread.cont).

Lemma mmt_id_exp_in mid_pfx labs lab
      (IN: Ensembles.In _ labs lab):
  Ensembles.In _ (mmt_id_exp mid_pfx labs) (mid_pfx ++ [lab]).
Proof. econs; eauto. rewrite app_nil_r. ss. Qed.

Lemma mmt_id_exp_call mid_pfx labs lab labs'
      (IN: Ensembles.In _ labs lab):
  Included _ (mmt_id_exp (mid_pfx ++ [lab]) labs') (mmt_id_exp mid_pfx labs).
Proof. ii. inv H. econs; eauto. rewrite <- app_assoc. ss. Qed.

Lemma mmt_id_exp_empty mid_pfx mids:
  Included _ (mmt_id_exp mid_pfx (Empty_set _)) mids.
Proof. ii. inv H. inv LAB. Qed.

Lemma bnd_ro envt mids rmap s
      (RO: EnvType.ro_judge envt s):
  bnd envt mids rmap s.
Proof. exists (Empty_set _). split; [right; ss|]. i. apply mmt_id_exp_empty. Qed.

Lemma bnd_rw envt mids rmap labs s
      (RW: EnvType.rw_judge envt labs s)
      (INCL: forall pfx, rmap mid = Some (Val.mid pfx) -> Included _ (mmt_id_exp pfx labs) mids):
  bnd envt mids rmap s.
Proof. exists labs. split; ss. left. apply EnvShape.rw_judge_forall. ss. Qed.

Lemma bnd_regs envt mids rmap rmap' s
      (MID: rmap' mid = rmap mid)
      (BND: bnd envt mids rmap s):
  bnd envt mids rmap' s.
Proof. destruct BND as (labs & TY & INCL). exists labs. split; ss. rewrite MID. ss. Qed.

Lemma bnd_cons_inv envt mids rmap x s
      (BND: bnd envt mids rmap (x :: s)):
  (exists labs labs',
      Included _ labs' labs
      /\ EnvShape.rw_shape envt labs' x
      /\ rw_stmts envt labs s
      /\ forall pfx, rmap mid = Some (Val.mid pfx) -> Included _ (mmt_id_exp pfx labs) mids)
  \/ (EnvShape.ro_shape envt x /\ EnvType.ro_judge envt s).
Proof.
  destruct BND as (labs & [TY | TY] & INCL).
  - inv TY. destruct H1 as (labs' & INCL' & RW). left. exists labs, labs'. splits; ss.
    apply EnvShape.rw_judge_single. ss.
  - apply ro_judge_cons in TY. destruct TY as [ONE REST]. right. split; ss.
    apply EnvShape.ro_judge_single. ss.
Qed.

Lemma bnd_rw_stmts envt mids rmap labs s
      (RW: rw_stmts envt labs s)
      (INCL: forall pfx, rmap mid = Some (Val.mid pfx) -> Included _ (mmt_id_exp pfx labs) mids):
  bnd envt mids rmap s.
Proof. exists labs. split; ss. left. ss. Qed.

Lemma rw_stmts_mon envt labs labs' s
      (INCL: Included _ labs labs')
      (RW: rw_stmts envt labs s):
  rw_stmts envt labs' s.
Proof.
  eapply Forall_impl; [|exact RW]. intros x (labs0 & INCL0 & RW0). exists labs0. split; ss.
  eapply included_trans; eauto.
Qed.

Lemma rw_judge_stmts envt labs labs' s
      (INCL: Included _ labs labs')
      (RW: EnvType.rw_judge envt labs s):
  rw_stmts envt labs' s.
Proof. eapply rw_stmts_mon; eauto. apply EnvShape.rw_judge_forall. ss. Qed.

Lemma midfree_reg r
      (NMID: r <> mid):
  midfree (expr_reg r).
Proof. intro FREE. ss. congr. Qed.

Lemma loop_head_rw envt r lab
      (NMID: r <> mid):
  EnvType.rw_judge envt (Singleton _ lab) [stmt_chkpt r [stmt_return (expr_reg r)] (expr_mid lab)].
Proof.
  econs; eauto.
  - econs.
  - split; ss. apply midfree_reg. ss.
Qed.

Local Ltac mid_neq := let EQ := fresh "EQ" in intro EQ; subst; eauto.

Lemma inv_step:
  forall env envt mids tr thr1 thr2,
    TypeSystem.env_ok env envt ->
    thr_inv envt mids thr1 ->
    Thread.step env tr thr1 thr2 ->
  thr_inv envt mids thr2
  /\ (forall m, ~ Ensembles.In _ mids m -> thr2.(Thread.mmts) m = thr1.(Thread.mmts) m)
  /\ (forall mmts1',
        (forall m, Ensembles.In _ mids m -> mmts1' m = thr1.(Thread.mmts) m) ->
      exists mmts2',
        Thread.step env tr
          (Thread.mk thr1.(Thread.stmt) thr1.(Thread.cont) thr1.(Thread.ts) mmts1')
          (Thread.mk thr2.(Thread.stmt) thr2.(Thread.cont) thr2.(Thread.ts) mmts2')
        /\ (forall m, Ensembles.In _ mids m -> mmts2' m = thr2.(Thread.mmts) m)
        /\ (forall m, ~ Ensembles.In _ mids m -> mmts2' m = mmts1' m)).
Proof.
  intros env envt mids tr thr1 thr2 [OK_RO OK_RW] [BND FRAMES] STEP.
  inv STEP; ss.
  - (* assign *)
    splits.
    + split; [|exact FRAMES].
      destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)].
      * ss. destruct SHAPE as [NMID _]. eapply bnd_regs; [|eapply bnd_rw_stmts; eauto].
        apply VRegMap.add_neq. mid_neq.
      * apply bnd_ro. ss.
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto.
  - (* pload *)
    splits.
    + split; [|exact FRAMES].
      destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)]; ss.
      apply bnd_ro. ss.
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto.
  - (* palloc *)
    splits.
    + split; [|exact FRAMES].
      destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)]; ss.
      apply bnd_ro. ss.
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto.
  - (* branch *)
    splits.
    + split; [|exact FRAMES].
      destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)].
      * ss. destruct SHAPE as (labs_t & labs_f & RW_T & RW_F & INCL_T & INCL_F & MF).
        eapply bnd_rw_stmts; eauto. apply Forall_app. split; ss.
        destruct b.
        -- eapply (@rw_judge_stmts envt labs_t labs); [eapply included_trans; eauto | exact RW_T].
        -- eapply (@rw_judge_stmts envt labs_f labs); [eapply included_trans; eauto | exact RW_F].
      * ss. destruct SHAPE as [RO_T RO_F]. apply bnd_ro. apply ro_judge_app. split; ss. destruct b; ss.
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto.
  - (* loop *)
    destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)].
    + assert (BODY: forall v', bnd envt mids (set_opt r v' (TState.regs ts)) s_body).
      { intro v'. destruct r as [r|]; ss.
        - destruct SHAPE as (lab & labs'' & s' & S_BODY & RW' & NIN & IN & INCL'' & NMID & MF). subst.
          eapply bnd_regs; [apply VRegMap.add_neq; mid_neq|].
          eapply bnd_rw_stmts; eauto. econs.
          + esplits; [|apply loop_head_rw; ss]. ii. inv H. eauto.
          + eapply (@rw_judge_stmts envt labs'' labs); [eapply included_trans; eauto | exact RW'].
        - destruct SHAPE as (E & labs'' & RW' & INCL''). subst.
          eapply bnd_rw_stmts; eauto.
          eapply (@rw_judge_stmts envt labs'' labs); [eapply included_trans; eauto | exact RW'].
      }
      splits.
      * split; [apply BODY|]. econs; [|exact FRAMES]. ss. split; [exact BODY | eapply bnd_rw_stmts; eauto].
      * ss.
      * intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto.
    + ss. splits.
      * split; [apply bnd_ro; ss|]. econs; [|exact FRAMES]. ss. split; [i; apply bnd_ro; ss | apply bnd_ro; ss].
      * ss.
      * intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto.
  - (* continue *)
    inversion FRAMES as [|? ? FR FRAMES']. subst. destruct FR as [FR_B FR_S].
    splits.
    + simpl. split; [apply FR_B | exact FRAMES].
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto.
  - (* break *)
    inversion FRAMES as [|? ? FR FRAMES']. subst. destruct FR as [FR_B FR_S].
    splits.
    + simpl. split; [exact FR_S | exact FRAMES'].
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto.
  - (* call *)
    destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)].
    + ss. destruct SHAPE as (es' & lab & ES & FN & IN & NMID & MF). subst.
      hexploit OK_RW; eauto. intros (prms0 & labs_f & s_f0 & FIND0 & RW_F & NODUP).
      rewrite FIND in FIND0. inv FIND0.
      hexploit sem_exprs_snoc; eauto. intros (vs' & v_m & VS & EVAL' & EVAL_M). subst.
      hexploit sem_expr_mid_inv; eauto. intros (pfx & MID & V_M). subst.
      rewrite ! app_length in ARITY. ss.
      splits.
      * split.
        -- eapply bnd_rw_stmts; [eapply rw_judge_stmts; [apply included_refl | eauto]|].
           intros pfx' MID'. simpl in MID'.
           rewrite bind_params_last in MID' by first [exact NODUP | lia]. inv MID'.
           eapply included_trans; [apply (@mmt_id_exp_call pfx labs lab labs_f); apply INCL'; exact IN |].
           apply INCL. exact MID.
        -- econs; ss. i. eapply bnd_regs; [apply VRegMap.add_neq; mid_neq|]. eapply bnd_rw_stmts; eauto.
      * ss.
      * intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto; rewrite ! app_length; ss; lia.
    + ss. hexploit OK_RO; eauto. intros (prms0 & s_f0 & FIND0 & RO_F & _). rewrite FIND in FIND0. inv FIND0.
      splits.
      * split; [apply bnd_ro; ss|]. econs; ss. i. apply bnd_ro. ss.
      * ss.
      * intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto.
  - (* return *)
    apply Forall_app in FRAMES. destruct FRAMES as [_ FRAMES].
    inversion FRAMES as [|? ? FR FRAMES']. subst.
    splits.
    + simpl. split; [apply FR | exact FRAMES'].
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss. eapply Thread.step_return; eauto.
  - (* chkpt_call *)
    destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)]; ss.
    destruct SHAPE as (lab & E_MID & IN & RO_C & NMID & MF). subst.
    hexploit sem_expr_mid_inv; eauto. intros (pfx & MID & M). inv M.
    assert (MID_IN: Ensembles.In _ mids (pfx ++ [lab])).
    { eapply INCL; eauto. apply mmt_id_exp_in. eauto. }
    splits.
    + split; [apply bnd_ro; ss|]. econs; ss. split; ss.
      i. eapply bnd_regs; [apply VRegMap.add_neq; mid_neq|]. eapply bnd_rw_stmts; eauto.
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss. econs; eauto. rewrite AGREE; ss.
  - (* chkpt_return *)
    apply Forall_app in FRAMES. destruct FRAMES as [_ FRAMES].
    inversion FRAMES as [|? ? FR FRAMES']. subst. destruct FR as [MID_IN FR].
    splits.
    + simpl. split; [apply FR | exact FRAMES'].
    + intros m' OUT. rewrite fun_add_spec. destruct (m' == m) as [EQ|NEQ]; ss. inv EQ. ss.
    + intros mmts1' AGREE. exists (fun_add m (Mmt.mk v t) mmts1'). splits.
      * eapply Thread.step_chkpt_return; eauto.
      * intros m' IN'. rewrite ! fun_add_spec. destruct (m' == m); ss. eauto.
      * intros m' OUT. rewrite fun_add_spec. destruct (m' == m) as [EQ|NEQ]; ss. inv EQ. ss.
  - (* chkpt_replay *)
    destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)]; ss.
    destruct SHAPE as (lab & E_MID & IN & RO_C & NMID & MF). subst.
    hexploit sem_expr_mid_inv; eauto. intros (pfx & MID & M). inv M.
    assert (MID_IN: Ensembles.In _ mids (pfx ++ [lab])).
    { eapply INCL; eauto. apply mmt_id_exp_in. eauto. }
    splits.
    + split; [|exact FRAMES]. eapply bnd_regs; [apply VRegMap.add_neq; mid_neq|]. eapply bnd_rw_stmts; eauto.
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss.
      rewrite <- (AGREE _ MID_IN). econs; eauto. rewrite AGREE; ss.
  - (* pcas_succ *)
    destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)]; ss.
    destruct SHAPE as (lab & E_MID & IN & NMID & MF_L & MF_O & MF_N). subst.
    hexploit sem_expr_mid_inv; eauto. intros (pfx & MID' & M). inv M.
    assert (MID_IN: Ensembles.In _ mids (pfx ++ [lab])).
    { eapply INCL; eauto. apply mmt_id_exp_in. eauto. }
    splits.
    + split; [|exact FRAMES]. eapply bnd_regs; [apply VRegMap.add_neq; mid_neq|]. eapply bnd_rw_stmts; eauto.
    + intros m' OUT. rewrite fun_add_spec. destruct (m' == pfx ++ [lab]) as [EQ|NEQ]; ss. inv EQ. ss.
    + intros mmts1' AGREE. exists (fun_add (pfx ++ [lab]) (Mmt.mk (Val.pair (Val.bool true) v_old) t) mmts1'). splits.
      * econs; eauto. rewrite AGREE; ss.
      * intros m' IN'. rewrite ! fun_add_spec. destruct (m' == pfx ++ [lab]); ss. eauto.
      * intros m' OUT. rewrite fun_add_spec. destruct (m' == pfx ++ [lab]) as [EQ|NEQ]; ss. inv EQ. ss.
  - (* pcas_fail *)
    destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)]; ss.
    destruct SHAPE as (lab & E_MID & IN & NMID & MF_L & MF_O & MF_N). subst.
    hexploit sem_expr_mid_inv; eauto. intros (pfx & MID' & M). inv M.
    assert (MID_IN: Ensembles.In _ mids (pfx ++ [lab])).
    { eapply INCL; eauto. apply mmt_id_exp_in. eauto. }
    splits.
    + split; [|exact FRAMES]. eapply bnd_regs; [apply VRegMap.add_neq; mid_neq|]. eapply bnd_rw_stmts; eauto.
    + intros m' OUT. rewrite fun_add_spec. destruct (m' == pfx ++ [lab]) as [EQ|NEQ]; ss. inv EQ. ss.
    + intros mmts1' AGREE. exists (fun_add (pfx ++ [lab]) (Mmt.mk (Val.pair (Val.bool false) v) t) mmts1'). splits.
      * eapply Thread.step_pcas_fail; eauto. rewrite AGREE; ss.
      * intros m' IN'. rewrite ! fun_add_spec. destruct (m' == pfx ++ [lab]); ss. eauto.
      * intros m' OUT. rewrite fun_add_spec. destruct (m' == pfx ++ [lab]) as [EQ|NEQ]; ss. inv EQ. ss.
  - (* pcas_replay *)
    destruct (bnd_cons_inv BND) as [(labs & labs' & INCL' & SHAPE & RW_S & INCL) | (SHAPE & RO_S)]; ss.
    destruct SHAPE as (lab & E_MID & IN & NMID & MF_L & MF_O & MF_N). subst.
    hexploit sem_expr_mid_inv; eauto. intros (pfx & MID' & M). inv M.
    assert (MID_IN: Ensembles.In _ mids (pfx ++ [lab])).
    { eapply INCL; eauto. apply mmt_id_exp_in. eauto. }
    splits.
    + split; [|exact FRAMES]. eapply bnd_regs; [apply VRegMap.add_neq; mid_neq|]. eapply bnd_rw_stmts; eauto.
    + ss.
    + intros mmts1' AGREE. exists mmts1'. splits; ss.
      rewrite <- (AGREE _ MID_IN). eapply Thread.step_pcas_replay; eauto. rewrite AGREE; ss.
Qed.

Lemma inv_rtc:
  forall env envt c mids tr thr1 thr2,
    TypeSystem.env_ok env envt ->
    Thread.rtc env c tr thr1 thr2 ->
    thr_inv envt mids thr1 ->
  thr_inv envt mids thr2
  /\ (forall m, ~ Ensembles.In _ mids m -> thr2.(Thread.mmts) m = thr1.(Thread.mmts) m)
  /\ (forall mmts1',
        (forall m, Ensembles.In _ mids m -> mmts1' m = thr1.(Thread.mmts) m) ->
      exists mmts2',
        Thread.rtc env c tr
          (Thread.mk thr1.(Thread.stmt) thr1.(Thread.cont) thr1.(Thread.ts) mmts1')
          (Thread.mk thr2.(Thread.stmt) thr2.(Thread.cont) thr2.(Thread.ts) mmts2')
        /\ (forall m, Ensembles.In _ mids m -> mmts2' m = thr2.(Thread.mmts) m)
        /\ (forall m, ~ Ensembles.In _ mids m -> mmts2' m = mmts1' m)).
Proof.
  intros env envt c mids tr thr1 thr2 OK RTC. induction RTC; intros INV.
  - splits; ss. intros mmts1' AGREE. exists mmts1'. splits; ss. econs 1.
  - subst. inv ONE. hexploit inv_step; eauto. intros (INV0 & OUT0 & FRAME0).
    hexploit IHRTC; eauto. intros (INV1 & OUT1 & FRAME1).
    splits; ss.
    + i. rewrite OUT1, OUT0; ss.
    + intros mmts1' AGREE.
      hexploit FRAME0; eauto. intros (mmts2' & STEP' & IN2 & OUT2).
      hexploit FRAME1; eauto. intros (mmts3' & RTC' & IN3 & OUT3).
      exists mmts3'. splits; ss.
      * eapply rtc_step; eauto.
      * i. rewrite OUT3, OUT2; ss.
Qed.

Lemma merge_in mids mmts mmts_a m
      (IN: Ensembles.In _ mids m):
  Mmts.merge mids mmts mmts_a m = mmts m.
Proof. unfold Mmts.merge. destruct (Mmts.mmts_in mids m); ss. Qed.

Lemma merge_out mids mmts mmts_a m
      (OUT: ~ Ensembles.In _ mids m):
  Mmts.merge mids mmts mmts_a m = mmts_a m.
Proof. unfold Mmts.merge. destruct (Mmts.mmts_in mids m); ss. Qed.

Lemma lift_mmt_gen:
  forall env envt labs s tr ts mmts s_w c_w ts_w mmts_w mids,
    TypeSystem.env_ok env envt ->
    EnvType.rw_judge envt labs s ->
    (forall pfx, ts.(TState.regs) mid = Some (Val.mid pfx) -> Included _ (mmt_id_exp pfx labs) mids) ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  Mmts.agree_on (Complement _ mids) mmts mmts_w
  /\ forall mmts_a,
      Thread.rtc env [] tr
        (Thread.mk s [] ts (Mmts.merge mids mmts mmts_a))
        (Thread.mk s_w c_w ts_w (Mmts.merge mids mmts_w mmts_a)).
Proof.
  intros env envt labs s tr ts mmts s_w c_w ts_w mmts_w mids OK RW INCL RTC.
  hexploit (@inv_rtc env envt [] mids); eauto.
  { split; [|econs]. eapply bnd_rw; eauto. }
  intros (_ & OUT & FRAME). ss. split.
  - intros m OUT_M. symmetry. apply OUT. ss.
  - intro mmts_a. hexploit (FRAME (Mmts.merge mids mmts mmts_a)).
    { i. apply merge_in. ss. }
    intros (mmts2' & RTC' & IN2 & OUT2).
    replace (Mmts.merge mids mmts_w mmts_a) with mmts2'; ss.
    funext. intro m. destruct (classic (Ensembles.In _ mids m)) as [IN | NIN].
    + rewrite merge_in; ss. eauto.
    + rewrite merge_out; ss. rewrite OUT2; ss. apply merge_out. ss.
Qed.

Lemma lift_mmt_ok:
  forall env envt labs s tr ts mmts s_w c_w ts_w mmts_w pfx,
    TypeSystem.env_ok env envt ->
    EnvType.rw_judge envt labs s ->
    ts.(TState.regs) mid = Some (Val.mid pfx) ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  Mmts.agree_on (Complement _ (mmt_id_exp pfx labs)) mmts mmts_w
  /\ forall mmts_a,
      Thread.rtc env [] tr
        (Thread.mk s [] ts (Mmts.merge (mmt_id_exp pfx labs) mmts mmts_a))
        (Thread.mk s_w c_w ts_w (Mmts.merge (mmt_id_exp pfx labs) mmts_w mmts_a)).
Proof.
  intros env envt labs s tr ts mmts s_w c_w ts_w mmts_w pfx OK RW MID RTC.
  eapply lift_mmt_gen; eauto. intros pfx' MID'. rewrite MID in MID'. inv MID'. apply included_refl.
Qed.

(* Lemma H.7 *)
Lemma lift_mmt:
  forall env envt labs s tr ts mmts s_w c_w ts_w mmts_w pfx,
    TypeSystem.judge env envt ->
    EnvType.rw_judge envt labs s ->
    ts.(TState.regs) mid = Some (Val.mid pfx) ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk s_w c_w ts_w mmts_w) ->
  Mmts.agree_on (Complement _ (mmt_id_exp pfx labs)) mmts mmts_w
  /\ forall mmts_a,
      Thread.rtc env [] tr
        (Thread.mk s [] ts (Mmts.merge (mmt_id_exp pfx labs) mmts mmts_a))
        (Thread.mk s_w c_w ts_w (Mmts.merge (mmt_id_exp pfx labs) mmts_w mmts_a)).
Proof. i. eapply lift_mmt_ok; eauto. apply TypeSystem.judge_env_ok. ss. Qed.

Definition top_loop (envt: EnvType.t) (base: option Val.t) (c: Cont.t) : Prop :=
  match c with
  | Cont.loopcont rmap r s_body s_cont =>
      rmap mid = base /\ r <> Some mid
      /\ (exists labs, rw_stmts envt labs s_body) /\ (exists labs, rw_stmts envt labs s_cont)
  | _ => False
  end.

Definition top_frame (envt: EnvType.t) (base: option Val.t) (c: Cont.t) : Prop :=
  match c with
  | Cont.fncont rmap r s_cont | Cont.chkptcont rmap r s_cont _ =>
      rmap mid = base /\ r <> mid /\ exists labs, rw_stmts envt labs s_cont
  | Cont.loopcont _ _ _ _ => False
  end.

Definition mid_inv (envt: EnvType.t) (base: option Val.t) (thr: Thread.t) : Prop :=
  (thr.(Thread.ts).(TState.regs) mid = base
   /\ (exists labs, rw_stmts envt labs thr.(Thread.stmt))
   /\ Forall (top_loop envt base) thr.(Thread.cont))
  \/ (exists c_up f c_top,
        thr.(Thread.cont) = c_up ++ f :: c_top
        /\ top_frame envt base f
        /\ Forall (top_loop envt base) c_top).

Lemma rw_stmts_cons_inv envt labs x s
      (RW: rw_stmts envt labs (x :: s)):
  (exists labs', Included _ labs' labs /\ EnvShape.rw_shape envt labs' x) /\ rw_stmts envt labs s.
Proof.
  inv RW. destruct H1 as (labs' & INCL & RWJ). split; ss.
  exists labs'. split; ss. apply EnvShape.rw_judge_single. ss.
Qed.

Lemma mid_step:
  forall env envt base tr thr1 thr2,
    TypeSystem.env_ok env envt ->
    mid_inv envt base thr1 ->
    Thread.step env tr thr1 thr2 ->
  mid_inv envt base thr2.
Proof.
  intros env envt pfx tr thr1 thr2 [OK_RO OK_RW] INV STEP.
  destruct INV as [(MID & (labs & RW) & LOOPS) | (c_up & f & c_top & CONT & FRAME & LOOPS)].
  - inv STEP; ss; apply rw_stmts_cons_inv in RW; destruct RW as [(labs' & INCL & SHAPE) RW]; ss.
    + left. destruct SHAPE as [NMID _]. splits; eauto. simpl. rewrite VRegMap.add_neq; [ss | mid_neq].
    + left. destruct SHAPE as (labs_t & labs_f & RW_T & RW_F & INCL_T & INCL_F & MF).
      splits; eauto. exists labs. apply Forall_app. split; ss.
      destruct b.
      * eapply (@rw_judge_stmts envt labs_t labs); [eapply included_trans; eauto | exact RW_T].
      * eapply (@rw_judge_stmts envt labs_f labs); [eapply included_trans; eauto | exact RW_F].
    + assert (BODY: exists labs0, rw_stmts envt labs0 s_body).
      { destruct r as [r|]; ss.
        - destruct SHAPE as (lab & labs'' & s' & S_BODY & RW' & NIN & IN & INCL'' & NMID & MF). subst.
          exists labs. econs.
          + esplits; [|apply loop_head_rw; ss]. ii. inv H. eauto.
          + eapply (@rw_judge_stmts envt labs'' labs); [eapply included_trans; eauto | exact RW'].
        - destruct SHAPE as (E & labs'' & RW' & INCL''). subst.
          exists labs. eapply (@rw_judge_stmts envt labs'' labs); [eapply included_trans; eauto | exact RW'].
      }
      assert (NMID: r <> Some mid).
      { destruct r as [r|]; ss. destruct SHAPE as (lab & labs'' & s' & S_BODY & RW' & NIN & IN & INCL'' & NMID & MF).
        ii. inv H. ss. }
      left. splits; eauto.
      * destruct r as [r|]; ss. simpl. rewrite VRegMap.add_neq; [ss | ii; subst; ss].
      * econs; ss. splits; eauto.
    + left. inversion LOOPS as [|? ? FR LOOPS']. subst. destruct FR as (MID' & NMID & BODY & REST).
      splits; eauto. destruct r as [r|]; ss. simpl. rewrite VRegMap.add_neq; [ss | ii; subst; ss].
    + left. inversion LOOPS as [|? ? FR LOOPS']. subst. destruct FR as (MID' & NMID & BODY & REST). splits; eauto.
    + right. destruct SHAPE as (es' & lab & ES & FN & IN & NMID & MF).
      exists [], (Cont.fncont (TState.regs ts) r s), c. splits; ss. splits; eauto.
    + apply Forall_app in LOOPS. destruct LOOPS as [_ LOOPS]. inv LOOPS. ss.
    + right. destruct SHAPE as (lab & E_MID & IN & RO & NMID & MF).
      exists [], (Cont.chkptcont (TState.regs ts) r s m), c. splits; ss. splits; eauto.
    + apply Forall_app in LOOPS. destruct LOOPS as [_ LOOPS]. inv LOOPS. ss.
    + left. destruct SHAPE as (lab & E_MID & IN & RO & NMID & MF). splits; eauto.
      simpl. rewrite VRegMap.add_neq; [ss | mid_neq].
    + left. destruct SHAPE as (lab & E_MID & IN & NMID & MF_L & MF_O & MF_N). splits; eauto.
      simpl. rewrite VRegMap.add_neq; [ss | mid_neq].
    + left. destruct SHAPE as (lab & E_MID & IN & NMID & MF_L & MF_O & MF_N). splits; eauto.
      simpl. rewrite VRegMap.add_neq; [ss | mid_neq].
    + left. destruct SHAPE as (lab & E_MID & IN & NMID & MF_L & MF_O & MF_N). splits; eauto.
      simpl. rewrite VRegMap.add_neq; [ss | mid_neq].
  - destruct thr1 as [s1 k1 ts1 mmts1]. ss. subst k1.
    assert (NLOOP_F: ~ Cont.Loops [f]).
    { intro L. inv L. destruct f; ss. }
    hexploit step_cont_cases; eauto.
    intros [(c0 & CONT0) | [(x & s_rem & CONT0 & LOOP & S1)
                           | (e & s_rem & c_loops & x & S1 & CONT0 & LOOPS0 & NLOOP_X)]].
    + right. exists (c0 ++ c_up), f, c_top. rewrite CONT0, app_assoc. splits; ss.
    + destruct c_up as [|y c_up]; ss.
      * injection CONT0 as X REST. subst x. exfalso. apply NLOOP_F. econs; [exact LOOP | econs].
      * injection CONT0 as Y REST. right. exists c_up, f, c_top. splits; ss.
    + hexploit frame_split; eauto.
      intros [(c1 & C_UP & REST) | [(L & c2 & C_BASE) | (C_UP & X & REST)]].
      * right. exists c1, f, c_top. splits; ss.
      * exfalso. apply Cont.loops_app_distr in L. destruct L as [_ L]. contradiction.
      * subst c_up s1. hexploit step_return_inv; eauto. intros [TR (v & EVAL & THR2)].
        left. destruct f; ss.
        -- destruct FRAME as (MID & NMID & labs & RW).
           rewrite THR2. simpl. splits; [rewrite VRegMap.add_neq; [ss | mid_neq] | eauto | try rewrite REST; ss].
        -- destruct FRAME as (MID & NMID & labs & RW). destruct THR2 as (t & TIME & THR2).
           rewrite THR2. simpl. splits; [rewrite VRegMap.add_neq; [ss | mid_neq] | eauto | try rewrite REST; ss].
Qed.

Lemma mid_rtc:
  forall env envt base c tr thr1 thr2,
    TypeSystem.env_ok env envt ->
    Thread.rtc env c tr thr1 thr2 ->
    mid_inv envt base thr1 ->
  mid_inv envt base thr2.
Proof.
  intros env envt pfx c tr thr1 thr2 OK RTC. induction RTC; ss.
  i. inv ONE. eapply IHRTC. eapply mid_step; eauto.
Qed.

Lemma rw_mid_top:
  forall env envt labs s tr ts mmts s_w ts_w mmts_w,
    TypeSystem.env_ok env envt ->
    EnvType.rw_judge envt labs s ->
    Thread.rtc env [] tr (Thread.mk s [] ts mmts) (Thread.mk s_w [] ts_w mmts_w) ->
  ts_w.(TState.regs) mid = ts.(TState.regs) mid.
Proof.
  intros env envt labs s tr ts mmts s_w ts_w mmts_w OK RW RTC.
  hexploit (@mid_rtc env envt (ts.(TState.regs) mid)); eauto.
  { left. splits; ss. exists labs. apply EnvShape.rw_judge_forall. ss. }
  intros [(MID' & _ & _) | (c_up & f & c_top & CONT & _ & _)]; ss.
  destruct c_up; ss.
Qed.
