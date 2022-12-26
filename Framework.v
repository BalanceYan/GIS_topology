Require Export Topology.

(* framework *)
Definition C_0 Y := Y = ∅.
Definition C_1 Y := ⦿ Y.

Definition Inter_bb A B X cT := Bound A X cT ∩ Bound B X cT.
Definition Inter_ii A B X cT := Interior A X cT ∩ Interior B X cT.
Definition Inter_bi A B X cT := Bound A X cT ∩ Interior B X cT.
Definition Inter_ib A B X cT := Interior A X cT ∩ Bound B X cT.

Definition r0 A B X cT :=
  C_0 (Inter_bb A B X cT) ∧ C_0 (Inter_ii A B X cT) ∧
  C_0 (Inter_bi A B X cT) ∧ C_0 (Inter_ib A B X cT).

Definition r1 A B X cT :=
  C_1 (Inter_bb A B X cT) ∧ C_0 (Inter_ii A B X cT) ∧
  C_0 (Inter_bi A B X cT) ∧ C_0 (Inter_ib A B X cT).

Definition r2 A B X cT :=
  C_0 (Inter_bb A B X cT) ∧ C_1 (Inter_ii A B X cT) ∧
  C_0 (Inter_bi A B X cT) ∧ C_0 (Inter_ib A B X cT).

Definition r3 A B X cT :=
  C_1 (Inter_bb A B X cT) ∧ C_1 (Inter_ii A B X cT) ∧
  C_0 (Inter_bi A B X cT) ∧ C_0 (Inter_ib A B X cT).

Definition r4 A B X cT :=
  C_0 (Inter_bb A B X cT) ∧ C_0 (Inter_ii A B X cT) ∧
  C_1 (Inter_bi A B X cT) ∧ C_0 (Inter_ib A B X cT).

Definition r5 A B X cT :=
  C_1 (Inter_bb A B X cT) ∧ C_0 (Inter_ii A B X cT) ∧
  C_1 (Inter_bi A B X cT) ∧ C_0 (Inter_ib A B X cT).

Definition r6 A B X cT :=
  C_0 (Inter_bb A B X cT) ∧ C_1 (Inter_ii A B X cT) ∧
  C_1 (Inter_bi A B X cT) ∧ C_0 (Inter_ib A B X cT).

Definition r7 A B X cT :=
  C_1 (Inter_bb A B X cT) ∧ C_1 (Inter_ii A B X cT) ∧
  C_1 (Inter_bi A B X cT) ∧ C_0 (Inter_ib A B X cT).

Definition r8 A B X cT :=
  C_0 (Inter_bb A B X cT) ∧ C_0 (Inter_ii A B X cT) ∧
  C_0 (Inter_bi A B X cT) ∧ C_1 (Inter_ib A B X cT).

Definition r9 A B X cT :=
  C_1 (Inter_bb A B X cT) ∧ C_0 (Inter_ii A B X cT) ∧
  C_0 (Inter_bi A B X cT) ∧ C_1 (Inter_ib A B X cT).

Definition r10 A B X cT :=
  C_0 (Inter_bb A B X cT) ∧ C_1 (Inter_ii A B X cT) ∧
  C_0 (Inter_bi A B X cT) ∧ C_1 (Inter_ib A B X cT).

Definition r11 A B X cT :=
  C_1 (Inter_bb A B X cT) ∧ C_1 (Inter_ii A B X cT) ∧
  C_0 (Inter_bi A B X cT) ∧ C_1 (Inter_ib A B X cT).

Definition r12 A B X cT :=
  C_0 (Inter_bb A B X cT) ∧ C_0 (Inter_ii A B X cT) ∧
  C_1 (Inter_bi A B X cT) ∧ C_1 (Inter_ib A B X cT).

Definition r13 A B X cT :=
  C_1 (Inter_bb A B X cT) ∧ C_0 (Inter_ii A B X cT) ∧
  C_1 (Inter_bi A B X cT) ∧ C_1 (Inter_ib A B X cT).

Definition r14 A B X cT :=
  C_0 (Inter_bb A B X cT) ∧ C_1 (Inter_ii A B X cT) ∧
  C_1 (Inter_bi A B X cT) ∧ C_1 (Inter_ib A B X cT).

Definition r15 A B X cT :=
  C_1 (Inter_bb A B X cT) ∧ C_1 (Inter_ii A B X cT) ∧
  C_1 (Inter_bi A B X cT) ∧ C_1 (Inter_ib A B X cT).

(* regularly closed *)
Definition RegClo A X cT := A = Closure (Interior A X cT) X cT.

Lemma RegClo_P : ∀ A B X cT, Ensemble X → Topology X cT →
  Closed A X cT → Closed B X cT → RegClo A X cT → RegClo B X cT →
  C_1 (Inter_bi A B X cT) → C_1 (Inter_ii A B X cT).
Proof.
  intros * Hxe Ht Ha Hb Har Hbr [x Hp]. assert (Has: A ⊂ X). apply Ha.
  AppC Hp; andH. assert (Heq: Bound A X cT = Bound (Interior A X cT) X cT).
  { eapply bound_F2 in Has as Hac; eauto. apply closure_T in Ha; auto.
    rewrite <- Ha in Hac. pose proof (interiorP A X cT) as Hai.
    eapply bound_F2 in Hai; eauto. rewrite interior_T2a, <- Har in Hai; auto.
    rewrite Hai in Hac at 1; clear Hai. pose proof (bound_T A X cT).
    pose proof (bound_T (Interior A X cT) X cT).
    rewrite interior_T2a in H2; auto. eapply unEq_inEm_idEq; eauto. }
  rewrite Heq in H; clear Heq. AppC H; destruct H as [_ [_ [Hx H]]].
  rewrite <- interior_T2a in H0; auto; [|apply Hb]. AppC H0.
  apply H in H0 as [H0 _]. apply EmptyNE in H0 as [y]. exists y.
  rewrite CommuI in H0; auto.
Qed.

Theorem r_4 : ∀ A B X cT, Ensemble X → Topology X cT → Closed A X cT →
  Closed B X cT → RegClo A X cT → RegClo B X cT → r4 A B X cT → False.
Proof.
  intros * Hxe Ht Ha Hb Har Hbr [_ [Hii [Hbi _]]].
  apply RegClo_P in Hbi as [x]; auto. rewrite Hii in H; exfalso0.
Qed.

Theorem r_5 : ∀ A B X cT, Ensemble X → Topology X cT → Closed A X cT →
  Closed B X cT → RegClo A X cT → RegClo B X cT → r5 A B X cT → False.
Proof.
  intros * Hxe Ht Ha Hb Har Hbr [_ [Hii [Hbi _]]].
  apply RegClo_P in Hbi as [x]; auto. rewrite Hii in H; exfalso0.
Qed.

Theorem r_8 : ∀ A B X cT, Ensemble X → Topology X cT → Closed A X cT →
  Closed B X cT → RegClo A X cT → RegClo B X cT → r8 A B X cT → False.
Proof.
  intros * Hxe Ht Ha Hb Har Hbr [_ [Hii [_ Hib]]].
  unfold Inter_ib in Hib; rewrite CommuI in Hib.
  apply RegClo_P in Hib as [x]; auto.
  unfold Inter_ii in Hii. rewrite CommuI in Hii.
  unfold Inter_ii in H. rewrite Hii in H; exfalso0.
Qed.

Theorem r_9 : ∀ A B X cT, Ensemble X → Topology X cT → Closed A X cT →
  Closed B X cT → RegClo A X cT → RegClo B X cT → r9 A B X cT → False.
Proof.
  intros * Hxe Ht Ha Hb Har Hbr [_ [Hii [_ Hib]]].
  unfold Inter_ib in Hib; rewrite CommuI in Hib.
  apply RegClo_P in Hib as [x]; auto.
  unfold Inter_ii in Hii. rewrite CommuI in Hii.
  unfold Inter_ii in H. rewrite Hii in H; exfalso0.
Qed.

Theorem r_12 : ∀ A B X cT, Ensemble X → Topology X cT → Closed A X cT →
  Closed B X cT → RegClo A X cT → RegClo B X cT → r12 A B X cT → False.
Proof.
  intros * Hxe Ht Ha Hb Har Hbr [_ [Hii [Hbi _]]].
  apply RegClo_P in Hbi as [x]; auto. rewrite Hii in H; exfalso0.
Qed.

Theorem r_13 : ∀ A B X cT, Ensemble X → Topology X cT → Closed A X cT →
  Closed B X cT → RegClo A X cT → RegClo B X cT → r13 A B X cT → False.
Proof.
  intros * Hxe Ht Ha Hb Har Hbr [_ [Hii [Hbi _]]].
  apply RegClo_P in Hbi as [x]; auto. rewrite Hii in H; exfalso0.
Qed.

(* planar spatial region *)
Definition Spatial A X cT := ⦿ A ∧ A ⊊ X ∧
  RegClo A X cT ∧ subConnect (Interior A X cT) cT.

Fact spa_NEmpty : ∀ A X cT, Ensemble X → Topology X cT →
  Spatial A X cT → ⦿ Interior A X cT.
Proof.
  intros * Hxe Ht [[x Hx] [_ [Ha _]]].
  DC (Interior A X cT = ∅); [|apply EmptyNE; auto].
  red in Ha; rewrite H, closure_T1 in Ha; auto; subst; exfalso0.
Qed.

Fact spa_NX : ∀ A X cT, Topology X cT →
  Closed A X cT → Spatial A X cT → Closure A X cT ≠ X.
Proof.
  intros * Ht Hc [_ [[] _]]. apply closure_T in Hc; auto.
  rewrite <- Hc; auto.
Qed.

Fact spa_Connect : ∀ A X cT, Ensemble X → Topology X cT →
  Spatial A X cT → subConnect A cT.
Proof.
  intros * Hxe Ht [_ [_ [Heq Hic]]]. rewrite Heq.
  apply scon_T3C2; auto. split; andG; auto. eapply interiorP.
Qed.

Lemma Spatial_P1 : ∀ A X cT, Ensemble X → Connected X cT → Topology X cT →
  Closed A X cT → Spatial A X cT → Bound A X cT ≠ ∅.
Proof.
  intros * Hxe Hxc Ht Hc [Hae [Hap [Har Hac]]]. assert (Ha: A ⊂ X). apply Hc.
  DC (Bound A X cT = ∅); auto.
  assert (disSubConnect (X - (Bound A X cT)) cT).
  { apply scon_T4C; auto. split; andG; auto; eapply resFam; eauto.
    apply spa_NEmpty; auto. split; andG; auto. eapply closure_T in Hc; auto.
    rewrite <- Hc; apply Hap. } assert (cT|X = cT).
  { AppE; [AppC H1; destruct H1 as [B []]; subst x| AppCG; Ens; exists x;
    andG; auto]; rewrite IncI; auto; apply Ht in H1; pow H1. }
  rewrite H, SetminEm in H0. red in H0; rewrite H1 in H0; auto.
Qed.

Theorem r_2 : ∀ A B X cT, Ensemble X → Connected X cT → Topology X cT →
  Closed A X cT → Closed B X cT → Spatial A X cT → Spatial B X cT →
  r2 A B X cT → False.
Proof.
  intros * Hxe Hxc Ht Hac Hbc Has Hbs [Hbb [Hii [Hbi Hib]]].
  assert (A ⊂ X ∧ B ⊂ X). { andG. apply Hac. apply Hbc. }
  destruct H as [Hax Hbx]. assert (A = Closure A X cT ∧ B = Closure B X cT).
  { andG; apply closure_T; auto. } destruct H as [Haeq Hbeq].
  assert (Hb: B ⊂ X - Bound A X cT).
  { intros x Hx. smG; auto. assert (Bound A X cT ∩ B = ∅).
    unfold C_0, Inter_bi in Hbi; unfold C_0, Inter_bb in Hbb. rewrite Hbeq,
      interior_Tb, Re4_ClInBo, DistribuLI, Hbi, Hbb, EmptyU; auto.
    DC (x ∈ Bound A X cT); auto. assert (x ∈Bound A X cT ∩ B); ens.
    rewrite H in H1; exfalso0. }
  assert (Habx: X - Bound A X cT ⊂ X). intros x Hx; smH; auto.
  assert (Hcbx: subConnect B (cT | (X - Bound A X cT))).
  { apply (scon_T1 B (X - Bound A X cT) X cT); auto.
    split; andG; auto. split; auto; eapply resFam; eauto.
    eapply spa_Connect; eauto. }
  assert (Hbso: B ⊂ Interior A X cT ∨ B ⊂ X - A).
  { rewrite Haeq at 2. apply (scon_T3 B (X - Bound A X cT)
      (cT | (X - Bound A X cT))); auto. eapply SubAxP; eauto. split; auto.
    eapply resFam; eauto. apply scon_T4; auto. split; auto.
    apply spa_NEmpty; auto. apply spa_NX; auto.
    rewrite subTop_T1; auto. split; auto. } orH.
  - assert (Bound B X cT ⊂ Interior A X cT).
    { eapply IncTran; eauto. rewrite Hbeq at 2. rewrite interior_Tb,
        Re4_ClInBo; auto. intros x Hx; apply UnionI'; auto. }
    apply Spatial_P1, EmptyNE in Hbs as [x]; auto.
    assert (x ∈ Interior A X cT ∩ Bound B X cT); ens.
    unfold C_0, Inter_ib in Hib. rewrite Hib in H2; exfalso0.
  - destruct Hii as [x Hx]. AppC Hx; andH.
    apply interior_F1, H in H1. smH. apply interior_F1 in H0; auto.
Qed.

Theorem r_0 : ∀ A B X cT, Ensemble X → Topology X cT →
  Closed A X cT → Closed B X cT → r0 A B X cT → A ∩ B = ∅.
Proof.
  intros * Hxe Ht Hac Hbc [Hbb [Hii [Hbi Hib]]];
  unfold C_0, Inter_bb, Inter_ii, Inter_bi, Inter_ib in *.
  assert (A ⊂ X ∧ B ⊂ X). { andG. apply Hac. apply Hbc. } destruct H.
  apply closure_T in Hac; apply closure_T in Hbc; auto.
  rewrite Hac, Hbc, interior_Tb, Re4_ClInBo, interior_Tb,
    Re4_ClInBo, DistribuLI, DistribuI, DistribuI,
    Hbb, Hii, Hbi, Hib, EmptyU, EmptyU; auto. 
Qed.

Theorem r_1 : ∀ A B X cT, Ensemble X → Topology X cT →
  Closed A X cT → Closed B X cT → r1 A B X cT →
  A ∩ B = Bound A X cT ∩ Bound B X cT.
Proof.
  intros * Hxe Ht Hac Hbc [Hbb [Hii [Hbi Hib]]];
  unfold C_0, Inter_ii, Inter_bi, Inter_ib in *.
  assert (A ⊂ X ∧ B ⊂ X). { andG. apply Hac. apply Hbc. } destruct H.
  apply closure_T in Hac; apply closure_T in Hbc; auto.
  rewrite Hac, Hbc at 1. rewrite interior_Tb, Re4_ClInBo, interior_Tb,
    Re4_ClInBo, DistribuLI, DistribuI, DistribuI, Hii, Hbi, Hib, EmptyU,
    CommuU, EmptyU, CommuU, EmptyU; auto.
Qed.

Theorem r_14 : ∀ A B X cT, Ensemble X → Topology X cT →
  Closed A X cT → Closed B X cT → r14 A B X cT →
  Interior A X cT ∩ Interior B X cT ≠ ∅ ∧ A ∩ B ≠ ∅.
Proof.
  intros * Hxe Ht Hac Hbc [Hbb [Hii [[x Hbi] [y Hib]]]].
  assert (A ⊂ X ∧ B ⊂ X). { andG. apply Hac. apply Hbc. } destruct H.
  apply closure_T in Hac; apply closure_T in Hbc; auto.
  AppC Hbi; AppC Hib; andH. andG. apply EmptyNE, Hii. apply EmptyNE.
  exists x. rewrite Hac, Hbc, interior_Tb,
    Re4_ClInBo, interior_Tb, Re4_ClInBo; ens.
Qed.

Theorem r_15 : ∀ A B X cT, Ensemble X → Topology X cT →
  Closed A X cT → Closed B X cT → r15 A B X cT →
  Interior A X cT ∩ Interior B X cT ≠ ∅ ∧ A ∩ B ≠ ∅.
Proof.
  intros * Hxe Ht Hac Hbc [Hbb [Hii [[x Hbi] [y Hib]]]].
  assert (A ⊂ X ∧ B ⊂ X). { andG. apply Hac. apply Hbc. } destruct H.
  apply closure_T in Hac; apply closure_T in Hbc; auto.
  AppC Hbi; AppC Hib; andH. andG. apply EmptyNE, Hii. apply EmptyNE.
  exists x. rewrite Hac, Hbc, interior_Tb,
    Re4_ClInBo, interior_Tb, Re4_ClInBo; ens.
Qed.

Lemma Spatial_P2 : ∀ A B X cT, Ensemble X → Topology X cT →
  Closed A X cT → Closed B X cT → Spatial A X cT → Spatial B X cT →
  C_1 (Inter_ii A B X cT) → C_0 (Inter_ib A B X cT) →
  Interior A X cT ⊂ Interior B X cT ∧ A ⊂ B.
Proof.
  intros * Hxe Ht Hac Hbc Has Hbs Hp1 Hp2. assert (A ⊂ X ∧ B ⊂ X).
  { andG. apply Hac. apply Hbc. } destruct H as [Hax Hbx].
  assert (A = Closure A X cT ∧ B = Closure B X cT).
  { andG; apply closure_T; auto. } destruct H as [Haeq Hbeq].
  assert (Hai: Interior A X cT ⊂ X). apply interiorP; auto.
  assert (Hbxs: Separation (Interior B X cT) (X - B) X cT).
  { assert (SubTop (X - Bound B X cT) X cT). split; auto. apply SetminSubI.
    rewrite Hbeq at 2. apply (separation_T (X - Bound B X cT) X cT Hxe H
      (Interior B X cT) (X - Closure B X cT)).
    rewrite bound_F3; auto; apply SetminSub1, closureP; auto.
    rewrite bound_F2; auto; apply SetminSub2; intros x Hx; ens.
    apply scon_T4; auto. split; auto. apply spa_NEmpty; auto.
    apply spa_NX; auto. }
  assert (Interior A X cT ⊂ Interior B X cT ∨ Interior A X cT ⊂ X - B).
  { eapply scon_T3; eauto. split; auto. apply Has. rewrite Hbeq at 2.
    rewrite subTop_T1; try split; auto. intros x Hx. smG.
    eapply interiorP; eauto. DC (x ∈ Bound B X cT); auto.
    assert (x ∈ Interior A X cT ∩ Bound B X cT). ens.
    unfold C_0, Inter_ib in Hp2. rewrite Hp2 in H0; exfalso0. } orH.
  - destruct Has as [_ [_ [Hra _]]]; destruct Hbs as [_ [_ [Hrb _]]].
    andG; auto. rewrite Hra, Hrb. apply closure_F2; auto. apply interiorP.
  - exfalso. destruct Hp1 as [x Hx]. AppC Hx; andH. apply H in H0; smH.
    apply interior_F1 in H1; auto.
Qed.

Theorem r_3 : ∀ A B X cT, Ensemble X → Topology X cT →
  Closed A X cT → Closed B X cT → Spatial A X cT → Spatial B X cT →
  r3 A B X cT → A = B.
Proof.
  intros * Hxe Ht Hac Hbc Has Hbs [Hbb [Hii [Hbi Hib]]]. apply IncAsym.
  eapply Spatial_P2; eauto. eapply (Spatial_P2 B A); eauto;
  unfold C_0, C_1, Inter_ii, Inter_ib, Inter_bi in *; rewrite CommuI; auto.
Qed.

Theorem r_6 : ∀ A B X cT, Ensemble X → Topology X cT →
  Closed A X cT → Closed B X cT → Spatial A X cT → Spatial B X cT →
  r6 A B X cT → A ⊂ Interior B X cT.
Proof.
  intros * Hxe Ht Hac Hbc Has Hbs [Hbb [Hii [Hbi Hib]]].
  assert (Hp: Interior A X cT ⊂ Interior B X cT ∧ A ⊂ B).
  apply Spatial_P2; auto. destruct Hp as [Hiab Hab]. assert (A ⊂ X ∧ B ⊂ X).
  andG. apply Hac. apply Hbc. destruct H as [Hax Hbx].
  assert (A = Closure A X cT ∧ B = Closure B X cT).
  andG; apply closure_T; auto. destruct H as [Haeq Hbeq].
  rewrite Haeq, bound_F2; auto. intros x Hx; unH; auto.
  assert (Bound A X cT ⊂ B).
  { eapply IncTran; eauto. rewrite Haeq at 2.
    rewrite bound_F2; auto. intros y Hy; ens. }
  rewrite Hbeq, bound_F2 in H0; auto. apply H0 in H as Hb; unH; auto.
  assert (x ∈ Bound A X cT ∩ Bound B X cT). ens.
  unfold C_0, Inter_bb in Hbb. rewrite Hbb in H2; exfalso0.
Qed.

Theorem r_7 : ∀ A B X cT, Ensemble X → Topology X cT → Closed A X cT →
  Closed B X cT → Spatial A X cT → Spatial B X cT → r7 A B X cT → A ⊂ B.
Proof.
  intros. destruct H5 as [Hbb [Hii [Hbi Hib]]]. eapply Spatial_P2; eauto.
Qed.

Theorem r_10 : ∀ A B X cT, Ensemble X → Topology X cT →
  Closed A X cT → Closed B X cT → Spatial A X cT → Spatial B X cT →
  r10 A B X cT → B ⊂ Interior A X cT.
Proof.
  intros * Hxe Ht Hac Hbc Has Hbs [Hbb [Hii [Hbi Hib]]].
  assert (Hp: Interior B X cT ⊂ Interior A X cT ∧ B ⊂ A).
  eapply (Spatial_P2 B A); eauto; unfold C_0, C_1, Inter_ii, Inter_ib,
    Inter_bi in *; rewrite CommuI; auto. destruct Hp as [Hiba Hba].
  assert (A ⊂ X ∧ B ⊂ X). andG. apply Hac. apply Hbc. destruct H as [Hax Hbx].
  assert (A = Closure A X cT ∧ B = Closure B X cT).
  andG; apply closure_T; auto. destruct H as [Haeq Hbeq].
  rewrite Hbeq, bound_F2; auto. intros x Hx; unH; auto.
  assert (Bound B X cT ⊂ A).
  { eapply IncTran; eauto. rewrite Hbeq at 2.
    rewrite bound_F2; auto. intros y Hy; ens. }
  rewrite Haeq, bound_F2 in H0; auto. apply H0 in H as Hb; unH; auto.
  assert (x ∈ Bound A X cT ∩ Bound B X cT). ens.
  unfold C_0, Inter_bb in Hbb. rewrite Hbb in H2; exfalso0.
Qed.

Theorem r_11 : ∀ A B X cT, Ensemble X → Topology X cT → Closed A X cT →
  Closed B X cT → Spatial A X cT → Spatial B X cT → r11 A B X cT → B ⊂ A.
Proof.
  intros. destruct H5 as [Hbb [Hii [Hbi Hib]]]. eapply (Spatial_P2 B A); eauto;
  unfold C_0, C_1, Inter_ii, Inter_ib, Inter_bi in *; rewrite CommuI; auto.
Qed.