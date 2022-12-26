Require Export Ensemble.

(* General topology *)

(* topological spaces *)
Definition Topology X cT := cT ⊂ cP(X) ∧
  X ∈ cT ∧ ∅ ∈ cT ∧ (∀ A B, A ∈ cT → B ∈ cT → A ∩ B ∈ cT) ∧
  (∀ cT1, cT1 ⊂ cT → ∪cT1 ∈ cT).

Definition inDiscrete X := [X] ⋃ [∅].
Definition Discrete X := cP(X).

Example inDiscreteT : ∀ X, Ensemble X → Topology X (inDiscrete X).
Proof.
  intros. unfold inDiscrete. repeat split; intros.
  intros x Hx; unH; sing H0; ens. AppCG; ens. apply EmptySub.
  AppCG; ens. AppCG; ens. apply IntSinEm; auto. apply EleUSinEm; auto.
Qed.

Example DiscreteT : ∀ X, Ensemble X → Topology X (Discrete X).
Proof.
  intros. unfold Discrete; repeat split; ens; intros.
  apply PowerI; auto; apply EmptySub. pow H0; pow H1. AppCG.
  apply InterEns; eens. intros x Hx; inH; auto.
  AppCG. eens. intros x Hx; eleU Hx; apply H0 in H2; pow H2.
Qed.

(* neighborhood system *)
Definition Neigh x U X cT := Topology X cT ∧ x ∈ X ∧ U ⊂ X ∧
  ∃ V, V ∈ cT ∧ x ∈ V ∧ V ⊂ U.
Definition NeighS x X cT := \{λ U, Neigh x U X cT\}.

Fact neighF : ∀ x U X cT, Topology X cT → x ∈ U → U ∈ cT → Neigh x U X cT.
Proof.
  intros. assert (U ⊂ X). apply H in H1; pow H1.
  red; andG; auto. exists U; andG; ens.
Qed.

Fact neigh_F1 : ∀ x U X cT,
  Ensemble X → Neigh x U X cT ↔ U ∈ NeighS x X cT.
Proof. split; intros. AppCG. eapply SubAxP; eauto. apply H0. AppC H0. Qed.

Definition EleUx x U cT := ∪\{λ V, x ∈ U ∧ V ∈ cT ∧ x ∈ V ∧ V ⊂ U \}.

Lemma Le_NeFa : ∀ U, U = ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}).
Proof.
  intro. AppE; AssE x. AppCG. exists [x]. andG; ens. AppCG; ens.
  eleU H. AppC H1; destruct H1; andH. subst. sing H; Ens.
Qed.

Theorem neigh_T : ∀ U X cT, Ensemble X → Topology X cT → U ⊂ X →
  (U ∈ cT ↔ ∀ x, x ∈ U → U ∈ NeighS x X cT).
Proof.
  intros * Hxe Ht Hs. split; intros Hp.
  - intros. apply neigh_F1, neighF; auto.
  - DC (U = ∅). subst; apply Ht. set (∪(\{λ t, ∃ x, x ∈ U ∧
      t = EleUx x U cT\})) as Hmi.
    assert (H1 : ∪(\{λ t, ∃ x, x ∈ U ∧ t = [x]\}) ⊂ Hmi).
    { intros z Hz; eleU Hz. AppC H1; destruct H1; andH. subst.
      sing H0; Ens. apply Hp in H1 as Hu. AppC Hu. AppCG; Ens.
      exists (EleUx x0 U cT). andG. AppCG; Ens. destruct Hu as
        [_ [_ [_ [V [Hv []]]]]]. exists V. andG; auto. AppCG; Ens. AppCG.
      apply (SubAxP U); eens. intros z Hz. eleU Hz. AppC H2; andH; auto. }
    rewrite <- Le_NeFa in H1. assert (H2 : Hmi ⊂ U).
    { intros z Hz. eleU Hz. AppC H2; destruct H2; andH.
      subst. eleU H0; AppC H3; andH; auto. } assert (U = Hmi). eens.
    rewrite H0. apply Ht; intros V Hv. AppC Hv; destruct Hv; andH.
    subst V. apply Ht. intros z Hz; AppC Hz; tauto.
Qed.

Theorem neigh_T1a : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U V, U ∈ NeighS x X cT → V ∈ NeighS x X cT →
  U ∩ V ∈ NeighS x X cT.
Proof.
  intros * Hxe Ht Hx * Hu Hv.
  apply neigh_F1 in Hu as [_ [_ [Hux [U0 [Ho1 []]]]]]; auto.
  apply neigh_F1 in Hv as [_ [_ [Hvx [V0 [Ho2 []]]]]]; auto.
  apply neigh_F1; auto. red; andG; auto. intros z Hz; inH; auto.
  exists (U0 ∩ V0). andG; ens. apply Ht; auto. intros z Hz; inH; ens.
Qed.

Theorem neigh_T1b : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U V, U ∈ NeighS x X cT → V ⊂ X → U ⊂ V → V ∈ NeighS x X cT.
Proof.
  intros * Hxe Ht Hx * Hu Hv Huv.
  apply neigh_F1 in Hu as [_ [_ [Hux [U0 [Ho1 []]]]]]; auto.
  apply neigh_F1; auto. red; andG; auto. exists U0; andG; eens.
Qed.

Theorem neigh_T1c : ∀ x X cT, Ensemble X → Topology X cT → x ∈ X →
  ∀ U, U ∈ NeighS x X cT → ∃ V, V ∈ NeighS x X cT ∧ V ⊂ U ∧
  (∀ y, y ∈ V → V ∈ NeighS y X cT).
Proof.
  intros. apply neigh_F1 in H2 as [_[_[Hu [V [Ho []]]]]]; auto. exists V.
  andG; auto. apply neigh_F1, neighF; auto. apply neigh_T; eens.
Qed.

(* derived *)
Definition Cluster x A X cT := Topology X cT ∧ A ⊂ X ∧ x ∈ X ∧
  ∀ U, Neigh x U X cT → U ∩ (A - [x]) ≠ ∅.
Definition Derived A X cT := \{λ x, Cluster x A X cT\}.

Fact DerivedP : ∀ A X cT, Derived A X cT ⊂ X.
Proof. intros * x Hx. AppC Hx. apply Hx. Qed.

Fact derived_F1 : ∀ x A X cT, Cluster x A X cT ↔ x ∈ Derived A X cT.
Proof. split; intros. AppCG; exists X; apply H. AppC H. Qed.

Fact derived_F2 : ∀ x A X cT, Topology X cT → A ⊂ X → x ∈ X →
  x ∉ Derived A X cT → ∃ U, Neigh x U X cT ∧ U ∩ (A - [x]) = ∅.
Proof.
  intros * Ht Hs Hx Hp. DC (∃ U, Neigh x U X cT ∧ U ∩ (A - [x]) = ∅).
  auto. elim Hp; apply derived_F1; red; andG; eauto.
Qed.

Theorem derived_Ta : ∀ A B X cT, B ⊂ X → A ⊂ B → Derived A X cT ⊂ Derived B X cT.
Proof.
  intros * Hb Hs x Hx. apply derived_F1 in Hx. red in Hx; andH.
  apply derived_F1. red; andG; auto. intros U Hu. apply H2 in Hu.
  apply EmptyNE in Hu as [y]. inH; smH.
  apply EmptyNE. exists y; inG; smG; auto.
Qed.

Theorem derived_Tb : ∀ A B X cT, Ensemble X → A ⊂ X → B ⊂ X →
  Derived (A ⋃ B) X cT = Derived A X cT ⋃ Derived B X cT.
Proof.
  intros * Hxe Ha Hb. apply IncAsym.
  - intros x Hx. pose proof Hx as Hx'. apply derived_F1 in Hx as
      [Ht [_ [Hx _]]]. DC (x ∈ Derived A X cT ⋃ Derived B X cT); auto.
    apply UnionNE in H; andH. apply derived_F2 in H as [U [Hun Hu]];
    apply derived_F2 in H0 as [V [Hvn Hv]]; auto.
    assert (x ∉ Derived (A ⋃ B) X cT).
    { intro. apply derived_F1 in H as [_ [_ [_ Hp]]]. set (U ∩ V) as D.
      assert (D ∈ NeighS x X cT). apply neigh_T1a; auto;
      apply neigh_F1; auto. apply neigh_F1, Hp in H; auto.
      assert (D ∩ (A ⋃ B) - [x] = ∅).
      { assert ((A ⋃ B) - [x] = A - [x] ⋃ B - [x]). AppE. smH; unH; ens.
        unH; smH; smG; ens. rewrite H0, DistribuLI. AppE; [|exfalso0].
        rewrite <- Hu, <- (EmptyU (U ∩ A - [x])), <- Hv.
        unH;inH;smH;AppC H1; andH; [unG|apply UnionI']; inG; smG; auto. }
       auto. } tauto.
  - assert (Derived A X cT ⊂ Derived (A ⋃ B) X cT ∧
      Derived B X cT ⊂ Derived (A ⋃ B) X cT).
    { andG; apply derived_Ta; intros x Hx; unH; ens. }
    andH; intros x Hx; unH; auto.
Qed.

Theorem derived_Tc : ∀ A X cT, Ensemble X → A ⊂ X →
  Derived (Derived A X cT) X cT ⊂ A ⋃ Derived A X cT.
Proof.
  intros * Hxe Ha x Hx. pose proof Hx as Hx'. apply derived_F1 in Hx as
    [Ht [_ [Hx _]]]. DC (x ∈ A ⋃ Derived A X cT); auto. exfalso.
  apply UnionNE in H as [Hxa Hxd]. apply derived_F2 in Hxd as
    [U [Hun Hue]]; auto. apply neigh_F1 in Hun as Hun'; auto.
  apply neigh_T1c in Hun' as [V [Hvn [Hvu Hp]]]; auto.
  apply neigh_T in Hp as Hp'; auto; [|apply neigh_F1 in Hvn; auto;
  eapply IncTran; eauto; apply Hun]. assert (V ∩ A - [x] = ∅).
  { AppE; [|exfalso0]. rewrite <- Hue. inH; smH. inG; smG; auto. }
  assert (V ∩ A = ∅). { eapply InterEqEmI; revgoals; eauto; Ens. }
  assert (∀ y, y ∈ V → y ∉ A).
  { intros * Hy H1. assert (y ∈ V ∩ A); ens. rewrite H0 in H2. exfalso0. }
  assert (∀ y, y ∈ V → V ∩ A - [y] = ∅).
  { intros. AppE; [|exfalso0]. inH; smH. apply H1 in H3; tauto. }
  assert (∀ y, y ∈ V → y ∉ Derived A X cT).
  { intros * Hy H3. apply H2 in Hy as Hyp. apply derived_F1 in H3.
    apply Hp, neigh_F1, H3 in Hy; auto. }
  assert (V ∩ Derived A X cT - [x] = ∅).
  { AppE; [|exfalso0]. inH; smH. exfalso. apply H3 in H4; auto. }
  apply derived_F1 in Hx' as [_ [_ [_ Hx']]].
  AppC Hvn. apply Hx' in Hvn; auto.
Qed.

(* Closed *)
Definition Closed A X cT := Topology X cT ∧ A ⊂ X ∧ Derived A X cT ⊂ A.

Theorem closed_T : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closed A X cT ↔ X - A ∈ cT.
Proof.
  intros * Hxe Ht Hs. pose proof (SetminSubI A X). split; intros Hp.
  - eapply neigh_T; eauto. intros. smH. assert (x ∉ Derived A X cT).
    { intro. apply Hp in H2; tauto. } apply derived_F2 in H2 as
      [U [Hun Hue]]; auto. apply InterEqEmI in Hue; Ens. 
    apply neigh_F1; auto. red; andG; auto. destruct Hun as
      [_ [_ [Hu [V [Hv [Hxv Hvu]]]]]]. exists V. andG; auto.
    eapply IncTran; eauto. intros z Hz. smG; auto. intro.
    assert (z ∈ U ∩ A); ens. rewrite Hue in H3; exfalso0.
  - red; andG; auto. intros x Hx. DC (x ∈ A); auto. exfalso.
    assert (x ∈ X - A). { AppC Hx. smG; auto. apply Hx. }
    eapply neigh_T, neigh_F1 in H1; eauto. pose proof Hx.
    apply derived_F1 in Hx as [_ [_ [_ Hx]]]. apply Hx in H1.
    assert (X-A ∩ A-[x] = ∅). AppE; [|exfalso0]; inH; smH; tauto. auto.
Qed.

Corollary closed_C : ∀ A X cT,
  Ensemble X → Topology X cT → A ⊂ X → A ∈ cT → Closed (X - A) X cT.
Proof.
  intros. apply closed_T; auto.
  apply SetminSubI. rewrite TwoCompl; auto.
Qed.

(* closure *)
Definition Closure A X cT := A ⋃ Derived A X cT.

Fact closureP : ∀ A X cT, A ⊂ X → Closure A X cT ⊂ X.
Proof. intros * Ha x Hx. AppC Hx; orH; auto. apply DerivedP in H; auto. Qed.

Fact closure_F1 : ∀ A X cT, A ⊂ Closure A X cT .
Proof. intros * x Hx. AppCG; Ens. Qed.

Fact closure_F2 : ∀ A B X cT, B ⊂ X → A ⊂ B → Closure A X cT ⊂ Closure B X cT.
Proof.
  unfold Closure; intros * Hb Hs x Hx. unH; ens.
  apply UnionI'. eapply derived_Ta; eauto.
Qed.

Fact closure_F3 : ∀ A B X cT, Ensemble X → Topology X cT →
  A ⊂ X → B ⊂ X → Closure (A ⋃ B) X cT = Closure A X cT ⋃ Closure B X cT.
Proof.
  intros * Hxe Ht Ha Hb. unfold Closure. rewrite derived_Tb,
    AssocU, (CommuU B), <- AssocU, <- AssocU, AssocU, (CommuU _ B); auto.
Qed.

Fact closure_F4 : ∀ A B X cT, Ensemble X → Topology X cT →
  A ⊂ X → B ⊂ X → Closure (A ⋃ B) X cT = Closure A X cT ⋃ Closure B X cT.
Proof.
  intros * Hxe Ht Ha Hb. unfold Closure. rewrite derived_Tb,
    AssocU, (CommuU B), <- AssocU, <- AssocU, AssocU, (CommuU _ B); auto.
Qed.

Theorem closure_T : ∀ A X cT, Topology X cT → A ⊂ X →
  Closed A X cT ↔ A = Closure A X cT.
Proof.
  intros * Ht Hs. split.
  - intros [_ [_ Hp]]. unfold Closure. AppE; [|unH]; ens.
  - intros. red; andG; auto. rewrite H at 2; intros z HZ; AppCG; Ens.
Qed.

Theorem closure_T1 : ∀ X cT, Ensemble X → Topology X cT → Closure ∅ X cT = ∅.
Proof.
  intros. pose proof (EmptySub X). symmetry; apply closure_T; auto.
  apply closed_T; auto. rewrite SetminEm; apply H0.
Qed.

Theorem closure_T2 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure (Closure A X cT) X cT = Closure A X cT.
Proof.
  intros * He Ht Hs. unfold Closure at 2. rewrite closure_F3; auto;
  [|apply DerivedP]. unfold Closure. rewrite AssocU,
    <- (AssocU (Derived A X cT) _ _), IdemU,
    <- AssocU, CommuU, IncU; auto. apply derived_Tc; auto.
Qed.

Fact closure_F5 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closed (Closure A X cT) X cT.
Proof.
  intros * Hxe Ht Hs. apply closure_T; auto.
  apply closureP; auto. rewrite closure_T2; auto.
Qed.

(* Interior *)
Definition Interiorp x A X cT := Neigh x A X cT.
Definition Interior A X cT := \{λ x, Interiorp x A X cT \}.

Fact interiorP : ∀ A X cT, Interior A X cT ⊂ X.
Proof.
  unfold Interior, Interiorp, Neigh.
  intros * z Hz. AppC Hz. andH. destruct H2; andH; auto.
Qed.

Fact interior_F1 : ∀ A X cT, Interior A X cT ⊂ A.
Proof.
  intros * z Hz. AppC Hz; destruct Hz; andH. destruct H2; andH; auto.
Qed.

Fact interior_F2 : ∀ A X cT, Interior A X cT ⊂ Closure A X cT.
Proof. intros. eapply IncTran. apply interior_F1. apply closure_F1. Qed.

Theorem interior_Ta : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Interior A X cT = X - (Closure (X - A) X cT).
Proof.
  intros * Hxe Ht Hs. apply IncAsym; intros x Hx.
  - AppC Hx. assert (Hx' := Hx).
    destruct Hx as [_ [Hx [_ [V [Hv [Hxv Hva]]]]]]. apply Hva in Hxv.
    AppCG; andG; Ens. intro. AppC H; orH. smH; auto. apply derived_F1 in H.
    apply H in Hx'. elim Hx'. AppE. inH; smH; tauto. exfalso0.
  - smH. apply UnionNE in H0 as [Hxi Hc]. apply derived_F2 in Hc as
      [V [Hnv Hc]]; auto; [|apply SetminSubI]. apply InterEqEmI in Hc; Ens.
    apply InterSetmin in Hc; [|apply Hnv]. AppCG; Ens.
    eapply neigh_F1, neigh_T1b; eauto. apply neigh_F1; auto.
Qed.

Theorem interior_Tb : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure A X cT = X - (Interior (X - A) X cT).
Proof.
  intros * Hxe Ht Hs. pose proof (SetminSubI A X) as Hc.
  eapply interior_Ta in Hc; eauto. erewrite TwoCompl in Hc; auto.
  apply (SetminEq _ _ X) in Hc. erewrite TwoCompl in Hc; auto.
  apply closureP; auto.
Qed.

Theorem interior_T1 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  A ∈ cT ↔ A = Interior A X cT.
Proof.
  intros * Hxe Ht Ha. pose proof SetminSubI A X as Hc. split; intros Hp.
  - eapply closed_C in Hp as Hp'; eauto.
    apply closure_T, (SetminEq _ _ X) in Hp'; auto.
    rewrite TwoCompl in Hp'; auto. rewrite interior_Ta; auto.
  - rewrite interior_Ta in Hp; auto. apply (SetminEq _ _ X) in Hp.
    rewrite TwoCompl in Hp; [|apply closureP]; auto.
    apply closure_T, closed_T in Hp; auto.
    rewrite TwoCompl in Hp; auto.
Qed.

Theorem interior_T2a : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Interior (Interior A X cT) X cT = Interior A X cT.
Proof.
  intros *Hxe Ht Ha. pose proof SetminSubI A X as Ha'.
  rewrite interior_Ta, interior_Ta, TwoCompl, closure_T2;
  auto. apply closureP; auto. apply interiorP.
Qed.

Theorem interior_T2b : ∀ A X cT,
  Ensemble X → Topology X cT → A ⊂ X → Interior A X cT ∈ cT.
Proof.
  intros * Hxe Ht Ha. eapply interior_T1; eauto.
  apply interiorP. symmetry; apply interior_T2a; auto.
Qed.

(* boundary *)
Definition Boundp x A X cT := Topology X cT ∧ A ⊂ X ∧ x ∈ X ∧
  ∀ U, Neigh x U X cT → U ∩ A ≠ ∅ ∧ U ∩ X - A ≠ ∅.
Definition Bound A X cT := \{λ x, Boundp x A X cT\}.

Fact boundP : ∀ A X cT, Bound A X cT ⊂ X.
Proof. intros * x Hx. AppC Hx; apply Hx. Qed.

Theorem bound_T : ∀ A X cT, Interior A X cT ∩ Bound A X cT = ∅.
Proof.
  intros. AppE; [exfalso|exfalso0]. inH. AppC H0. AppC H; apply H0 in H.
  andH. apply H1. AppE; [exfalso|exfalso0]. inH; smH; auto.
Qed.

Theorem Re1_ClInBo : ∀ A X cT, Topology X cT → A ⊂ X →
  Bound A X cT = Closure A X cT ∩ Closure (X - A) X cT.
Proof.
  intros * Ht Ha. pose proof SetminSubI A X as Ha'. AppE.
  - AppC H. red in H; andH. AppCG; Ens. andG; AppCG; Ens;
    [DC (x ∈ A); auto|DC (x ∈ X - A); auto]; right; apply derived_F1;
    red; andG; auto; intros; [apply H2 in H4 as [Hl _]|
    apply H2 in H4 as [_ Hl]]; intro; elim Hl; eapply InterEqEmI; Ens.
  - inH. AppCG; Ens. red; andG; auto. eapply closureP; eauto. intros.
    AppC H; AppC H0; orH; [smH; tauto|apply derived_F1 in H|
    apply derived_F1 in H0|].
    + andG. apply H in H1; intro; elim H1; apply InterEqEmE; auto.
      destruct H1 as [_ [_ [_ [V [_ [Hv Hvu]]]]]]. intro.
      assert (x ∈ U ∩ X - A); ens. rewrite H1 in H2; exfalso0.
    + andG; [|apply H0 in H1; intro; elim H1; apply InterEqEmE; auto].
      destruct H1 as [_ [_ [_ [V [_ [Hv Hvu]]]]]]. intro.
      assert (x ∈ U ∩ A); ens. rewrite H1 in H2; exfalso0.
    + apply derived_F1 in H; apply derived_F1 in H0. andG; [apply H in H1|
      apply H0 in H1]; intro; elim H1; apply InterEqEmE; auto.
Qed.

Theorem Re2_ClInBo : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure A X cT ∩ Closure (X - A) X cT =
  X - (Interior A X cT ⋃ Interior (X - A) X cT).
Proof.
  intros * Hxe Ht Ha. rewrite interior_Tb, interior_Tb,
    TwoCompl, <- UnionCompl, CommuU;
  try apply interiorP; auto. apply SetminSubI.
Qed.

Theorem Re3_ClInBo : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  X - (Interior A X cT ⋃ Interior (X - A) X cT) = Bound (X - A) X cT.
Proof.
  intros * Hxe Ht Ha. rewrite Re1_ClInBo, TwoCompl,
    CommuI, Re2_ClInBo; auto. apply SetminSubI.
Qed.

Theorem Re4_ClInBo : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  X - (Interior (X - A) X cT) = Interior A X cT ⋃ Bound A X cT.
Proof.
  intros * Hxe Ht Ha. rewrite Re1_ClInBo, DistribuLU, CommuU, CommuU, IncU,
    (interior_Tb (X - A) _ _), TwoCompl, ComUn, IncI, interior_Tb; auto.
  apply closureP; auto. apply interiorP; auto. apply SetminSubI.
  apply (IncTran _ A). intros * z Hz. AppC Hz; destruct Hz; andH.
  destruct H2; andH; auto. intros * x Hx. AppCG; Ens.
Qed.

Theorem Re5_ClInBo : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  X - (Closure (X - A) X cT) = Closure A X cT - Bound A X cT.
Proof.
  intros * Hxe Ht Ha. rewrite Re1_ClInBo, TwoDMI, SetminId, CommuU, EmptyU,
   (SetminInter (Closure A X cT) _ X), <- interior_Ta, CommuI, IncI; auto.
  apply interior_F2. apply closureP; auto.
Qed.

Fact bound_F1 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Bound A X cT = Bound (X - A) X cT.
Proof. intros. rewrite Re1_ClInBo, Re2_ClInBo, Re3_ClInBo; auto. Qed.

Fact bound_F2 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure A X cT = Interior A X cT ⋃ Bound A X cT.
Proof. intros. rewrite interior_Tb, Re4_ClInBo; auto. Qed.

Fact bound_F3 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Interior A X cT = Closure A X cT - Bound A X cT.
Proof. intros. rewrite interior_Ta, Re5_ClInBo; auto. Qed.

Corollary Re_bou_C1 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Closure A X cT = A ⋃ Bound A X cT.
Proof.
  intros. assert (A ⋃ Closure (X - A) X cT = X).
  { AppE. unH; auto. eapply closureP; revgoals; eauto. apply SetminSubI.
    DC (x ∈ A); ens. apply UnionI'. AppCG; Ens. left; ens. }
  rewrite Re1_ClInBo, DistribuLU, CommuU, CommuU, IncU, H2, IncI; auto.
  apply closureP; auto. apply closure_F1.
Qed.

Corollary Re_bou_C2 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Interior A X cT = A - Bound A X cT.
Proof.
  intros. pose proof (SetminSubI A X). assert (A ∩ X - Closure A X cT = ∅).
  { rewrite Re_bou_C1, TwoDMU; auto. AppE; [|exfalso0]. inH; smH; tauto. }
  erewrite Re1_ClInBo, SetminIE, InterCompl, DistribuLI, <- interior_Ta,
    H3, CommuU, EmptyU, CommuI, IncI; eauto; try apply closureP; auto;
  [|intros x Hx; inH; eapply closureP; eauto]. apply interior_F1.
Qed.

Corollary Re_bou_C3 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Bound (Interior A X cT) X cT ⊂ Bound A X cT.
Proof.
  intros. pose proof (SetminSubI A X). assert (Hai: Interior A X cT ⊂ A).
  apply interior_F1. rewrite Re1_ClInBo, Re1_ClInBo,
    <- (closure_T2 (X - A)); eens. intros x Hx; inH; inG.
  apply (closure_F2 (Interior A X cT)); auto.
  apply (closure_F2 (X - Interior A X cT)); auto. apply closureP; auto.
  rewrite Re_bou_C2, (SetminIE A (Bound A X cT) X), TwoDMI, TwoCompl,
    Re_bou_C1, bound_F1; auto; try apply boundP. intros y Hy; unH; ens.
Qed.

Corollary Re_bou_C4 : ∀ A X cT, Ensemble X → Topology X cT → A ⊂ X →
  Bound (Closure A X cT) X cT ⊂ Bound A X cT.
Proof.
  intros. rewrite Re1_ClInBo, Re1_ClInBo, closure_T2; auto;
  [|apply closureP; auto]. intros x Hx; inH. inG; ens.
  apply (closure_F2 (X - Closure A X cT) (X - A)); auto.
  apply SetminSubI. apply SetminSub2, closure_F1.
Qed.

(* subSpace *)
Definition RestFamEns cA Y := \{λ z, ∃ A, A ∈ cA ∧ z = A ∩ Y\}.
Notation "cA | Y" := (RestFamEns cA Y)(at level 30).

Lemma resFam : ∀ Y X cT, Ensemble X → Topology X cT → Y ⊂ X → Topology Y (cT|Y).
Proof.
  intros * Hxe Ht Hsub. split; andG.
  - intros z Hz. AppC Hz. destruct Hz as [A []].
    subst. assert (A ∩ Y ⊂ Y). intros x Hx; AppC Hx; tauto. eens.
  - AppCG; eens. exists X. andG. apply Ht. AppE; [|inH]; ens.
  - AppCG; ens. exists ∅. andG. apply Ht. AppE; [|inH]; exfalso0.
  - intros * Ha Hb. AppC Ha; AppC Hb.
    destruct Ha as [A' []], Hb as [B' []].
    subst. rewrite <- DisLII. AssE A'; AssE B'. AppCG.
    apply InterEns; eens. exists (A' ∩ B'). andG; auto. apply Ht; auto.
  - intros. assert (Hct: ∪cT1 ⊂ Y).
    { intros x Hx. eleU Hx. apply H in H1. AppC H1.
      destruct H1; andH. subst. inH; auto. } assert (Hp : ∀ A, A ∈ cT1 →
       ∃ A', [A,A'] ∈ \{\λ m n, n ∈ cT ∧ m = n ∩ Y\}\).
    { intros. AssE A. apply H in H0. AppC H0; destruct H0 as [A' []].
      AssE A'. exists A'. AppCG. ens. }
    assert (Hpe : Ensemble \{\λ m n, n ∈ cT ∧ m = n ∩ Y\}\).
    { assert (Hpe : \{\λ m n, n ∈ cT ∧ m = n ∩ Y\}\ ⊂ cP(X) × cT).
      { intros z Hz. PP Hz A B; andH. apply CProdI; auto.
        assert (A ⊂ X). subst; intros z Hz; inH; auto. ens. }
      eapply SubAxP; revgoals; eauto. apply CProdEns; ens.
      destruct Ht as [Ht _]. eens. }
    destruct (ChoAx1 _ _ Hpe Hp) as [f [Hf Hfp]].
    set (\{λ W, ∃ A, A ∈ cT1 ∧ W = f[A] ∩ Y\}) as cW.
    assert (Ht1: ∪cT1 = ∪cW).
    { AppE; eleU H0.
      - AppCG; andG; Ens. exists x0; andG; auto. AppCG; Ens.
        exists x0; andG; auto. apply Hfp in H1. AppC' H1; tauto.
      - AppC H1; destruct H1 as [A []]. apply Hfp in H1 as Ha.
        AppC' Ha; andH. AppCG; Ens. rewrite H2, <- H4 in H0; eauto. }
    set (\{λ V, ∃ A, A ∈ cT1 ∧ V = f[A]\}) as cV.
    assert (Ht2: ∪cW = (∪cV) ∩ Y).
    { AppE.
      - eleU H0. AppC H1; destruct H1 as [A []]. rewrite H2 in H0; inH.
        inG; auto. AppCG; Ens. exists f[A]; andG; auto. AppCG; eens.
      - inH. eleU H0. AppC H2; destruct H2 as [A []]. subst. AppCG; Ens.
        exists (f[A] ∩ Y). andG; ens. AppCG. apply InterEns; eens. }
    AppCG. eapply SubAxP; revgoals; eens. exists (∪ cV).
    rewrite Ht1, Ht2; andG; auto. apply Ht.
    intros A Ha. AppC Ha. destruct Ha as [B []]; andH.
    apply Hfp in H0. AppC' H0; andH. subst; auto.
Qed.

Definition SubTop Y X cT := Topology X cT ∧ Y ⊂ X.

Fact sTop_F1 : ∀ X Y cT, SubTop Y X cT →
  ∀ U, U ∈ cT|Y ↔ ∃ V, V ∈ cT ∧ U = V ∩ Y.
Proof.
  intros * [Ht Hs] *. split; intros. AppC H. destruct H as [V []].
  AssE V; AppCG. eapply SubAxP; eauto. intros x Hx; subst; inH; auto.
Qed.

Fact sTop_F2 : ∀ X Y Z cT,
  Ensemble X → SubTop Y X cT → SubTop Z Y (cT|Y) → SubTop Z X cT.
Proof. intros * Hxe [Hyt Hyx] [Hzt Hzy]. split; eens. Qed.

Theorem subTop_T1 : ∀ Y X cT, Ensemble X → SubTop Y X cT →
  Interior Y X cT ⋃ X - Closure Y X cT = X - Bound Y X cT.
Proof.
  intros * Hxe []. assert (Hix: Interior Y X cT ⊂ X). apply interiorP.
  rewrite bound_F2, UnionCompl, DistribuLU, ComUn, CommuI, IncI, IncU;
  auto. rewrite bound_F3; auto. apply SetminSub1, closureP; auto.
  intros x Hx; unH; ens. eapply SetminSubI; eauto. apply boundP.
Qed.

Theorem subTop_T2a : ∀ X Y cT, Ensemble X → SubTop Y X cT →
  ∀ y, y ∈ Y → NeighS y Y (cT|Y) = NeighS y X cT | Y.
Proof.
  intros * Hxe [Hxm Hs] * Hy. apply ExtAx; intro U; split; intros Hu.
  - AppCG; Ens. eapply neigh_F1 in Hu as [_ [_ [Hu [V [Hv [Hyv Hvu]]]]]];
    eens. AppC Hv. destruct Hv as [V1 [Hv1 Hvv]]. exists (V1 ⋃ U); andG;
    [|rewrite DistribuI, <- Hvv, IncI, IncU; auto].
    AppCG. apply UnionAx. Ens. eens. split; andG; auto.
    + intros x Hx. AppC Hx; orH; auto. apply Hxm in Hv1; pow Hv1.
    + exists V1. andG; auto. rewrite Hvv in Hyv; inH; auto. intros x Hx; AppCG; Ens.
  - AppCG; Ens. AppC Hu; destruct Hu as [A [Ha Hu]]. split; andG; auto.
    eapply resFam; eauto. subst; intros x Hx; inH; auto.
    eapply neigh_F1 in Ha as [_ [_ [Ha [V [Hv [Hyv Hva]]]]]]; eens.
    exists (V ∩ Y). rewrite Hu. andG; ens; [|intros x Hx; inH; ens].
    AppCG. apply InterEns; eens.
Qed.

Theorem subTop_T2b : ∀ X Y cT, Ensemble X → SubTop Y X cT →
  ∀ A, A ⊂ Y → Derived A Y (cT|Y) = Derived A X cT ∩ Y.
Proof.
  intros * Hxe [Hxm Hs] * Ha. AppE.
  - apply derived_F1 in H as [_ [_ [Hx Hxp]]]. inG; auto.
    apply derived_F1. split; andG; eens. intros. apply neigh_F1 in H; auto.
    assert (Neigh x (U ∩ Y) Y (cT | Y)).
    { apply neigh_F1; eens. erewrite subTop_T2a; eauto; [|split; auto].
      AppCG. eapply SubAxP; eauto. intros y Hy; inH; auto. }
    apply Hxp in H0. apply EmptyNE in H0 as [y]; inH.
    apply EmptyNE; exists y; ens.
  - inH. apply derived_F1 in H as [_ [_ [_ Hxp]]]. apply derived_F1.
    split; andG; auto. eapply resFam; eauto. intros V Hv.
    apply neigh_F1 in Hv; eens. erewrite subTop_T2a in Hv; eauto;
    [|split; auto]. AppC Hv; destruct Hv as [U [Hu Hvu]].
    apply neigh_F1, Hxp in Hu; auto. subst. rewrite AssocI, (CommuI Y),
      <- AssocI, IncI; auto. intros y Hy. inH; smH; auto.
Qed.

Theorem subTop_T2c : ∀ X Y cT, Ensemble X → SubTop Y X cT →
  ∀ A, A ⊂ Y → Closure A Y (cT|Y) = Closure A X cT ∩ Y.
Proof.
  intros * Hxe Hst * Ha. unfold Closure. erewrite subTop_T2b; eauto.
  rewrite <- (IncU A Y) at 2; auto. apply DistribuLU.
Qed.

(* connectedness *)
Definition Separation A B X cT :=
  A ⊂ X ∧ B ⊂ X ∧ (A ∩ Closure B X cT) ⋃ (B ∩ Closure A X cT) = ∅.

Fact sep_F1 : ∀ A B X cT, Separation A B X cT →
  A ∩ Closure B X cT = ∅ ∧ B ∩ Closure A X cT = ∅.
Proof. intros. apply two_union_Empty, H. Qed.

Fact sep_F2 : ∀ A B X cT, A ⊂ X → B ⊂ X → A ∩ Closure B X cT = ∅ →
  B ∩ Closure A X cT = ∅ → Separation A B X cT .
Proof. intros. split; andG; auto. apply two_union_Empty; auto. Qed.

Fact sep_F3 : ∀ A B X cT, Separation A B X cT →
  A ∩ B = ∅ ∧ A ∩ Derived B X cT = ∅.
Proof.
  intros. apply sep_F1 in H as [H _]. unfold Closure in H.
  rewrite DistribuLI in H. apply two_union_Empty in H; auto.
Qed.

Theorem separation_T : ∀ Y X cT, Ensemble X → SubTop Y X cT → ∀ A B,
  A ⊂ Y → B ⊂ Y → Separation A B Y (cT|Y) ↔ Separation A B X cT.
Proof.
  intros * Hxe Hst * Ha Hb.
  assert (Hp1: A ∩ Closure B Y (cT|Y) = A ∩ Closure B X cT).
  erewrite subTop_T2c, (CommuI _ Y), <- AssocI, (IncI A); eauto.
  assert (Hp2: B ∩ Closure A Y (cT|Y) = B ∩ Closure A X cT).
  erewrite subTop_T2c, (CommuI _ Y), <- AssocI, (IncI B); eauto.
  assert (Y ⊂ X). apply Hst. unfold Separation; rewrite Hp1, Hp2.
  split; intros; andH; andG; auto; eapply IncTran; eauto.
Qed.

Definition disConnected X cT :=
  ∃ A B, ⦿ A ∧ ⦿ B ∧ Separation A B X cT ∧ X = A ⋃ B.

Definition Connected X cT := ~ (disConnected X cT).

Theorem nConnect_Ta : ∀ X cT, Topology X cT → disConnected X cT →
  ∃ A B, ⦿ A ∧ ⦿ B ∧ Closed A X cT ∧ Closed B X cT ∧
  A ∩ B = ∅ ∧ A ⋃ B = X.
Proof.
  intros * Ht [A [B [Hae [Hbe [Hp1 Hp2]]]]]. assert (Heq: A ∩ B = ∅).
  { apply sep_F3 in Hp1; tauto. } pose proof Hp1.
  apply sep_F1 in H as [Hab Hba]. assert (A ⊂ X ∧ B ⊂ X).
  andG; apply Hp1. destruct H as [Has Hbs]. exists A, B. andG; auto;
  apply closure_T; auto; [rewrite <- (IncI (Closure A X cT) X)|
  rewrite <- (IncI (Closure B X cT) X)]; try apply closureP; auto;
  rewrite Hp2 at 2; rewrite CommuI, DistribuI; [rewrite Hba|
  rewrite Hab, CommuU]; rewrite EmptyU, IncI; auto; apply closure_F1.
Qed.

Theorem nConnect_Tb : ∀ X cT, Ensemble X → Topology X cT → (∃ A B,
  ⦿ A ∧ ⦿ B ∧ Closed A X cT ∧ Closed B X cT ∧ A ∩ B = ∅ ∧ A ⋃ B = X) →
  (∃ A B, ⦿ A ∧ ⦿ B ∧ A ∈ cT ∧ B ∈ cT ∧ A ∩ B = ∅ ∧ A ⋃ B = X).
Proof.
  intros * Hxe Ht [A [B [Hae [Hbe [Hba [Hbb [Hp1 Hp2]]]]]]].
  assert (A ⊂ X ∧ B ⊂ X). andG; [apply Hba|apply Hbb].
  destruct H as [Has Hbs]. apply closed_T in Hba; auto.
  apply closed_T in Hbb; auto. assert (A = X - B ∧ B = X - A).
  { andG; apply two_inter_Empty; auto; [rewrite CommuI|rewrite CommuU]; auto. }
  andH. exists A, B; andG; auto; [rewrite H|rewrite H0]; auto.
Qed.

Theorem nConnect_Tc : ∀ X cT, Ensemble X → Topology X cT →
  (∃ A B, ⦿ A ∧ ⦿ B ∧ A ∈ cT ∧ B ∈ cT ∧ A ∩ B = ∅ ∧ A ⋃ B = X) →
  (∃ C, ⦿ C ∧ C ⊊ X ∧ C ∈ cT ∧ Closed C X cT).
Proof.
  intros * Hxe Ht [A [B [Hae [Hbe [Hao [Hbo [Hp1 Hp2]]]]]]].
  apply Ht in Hao as Has; apply Ht in Hbo as Hbs. pow Has; pow Hbs.
  eapply two_inter_Empty in Hp1 as Hab; eauto. exists A; andG; auto. split; auto.
  { DC (A = X); auto. assert (B = ∅). rewrite (two_inter_Empty B A X); eauto;
    [|rewrite CommuI|rewrite CommuU]; auto. rewrite H; apply SetminId.
    destruct Hbe as [x]. subst B; exfalso0. }
  rewrite Hab; apply closed_C; auto.
Qed.

Theorem nConnect_Td : ∀ X cT, Ensemble X → Topology X cT →
  (∃ C, ⦿ C ∧ C ⊊ X ∧ C ∈ cT ∧ Closed C X cT) → disConnected X cT.
Proof.
  intros * Hxe Ht [A [Hae [[_ Hneq] [Hao Hac]]]]. set (B := X - A).
  assert (Has: A ⊂ X). apply Hac. assert (Hab: A ∩ B = ∅). apply ComIn.
  apply closed_T in Hac as Hbo; auto. eapply closed_C in Hao as Hbc; eauto.
  assert (Hbs: B ⊂ X). apply SetminSubI. exists A, B. andG; auto;
  [| |symmetry; apply ComUn; auto].
  { DC (⦿ B); auto. exfalso. apply EmptyEq in H. assert (A = X).
    { AppE; auto. DC (x ∈ A); auto. assert (x ∈ B).
      AppCG; Ens.  rewrite H in H2; exfalso0. } auto. } split; andG; auto;
  apply two_union_Empty; unfold Closure. repeat rewrite CommuU, IncU; andG; auto;
  [|apply Hac|apply Hbc]. rewrite CommuI; auto.
Qed.

Definition subConnect Y cT := Connected Y (cT|Y).
Definition disSubConnect Y cT := disConnected Y (cT|Y).

Theorem scon_T1 : ∀ Y Z X cT, Ensemble X → SubTop Z X cT →
  SubTop Y Z (cT|Z) → subConnect Y cT ↔ subConnect Y (cT|Z).
Proof.
  intros * Hxe Hzt Hyt. eapply sTop_F2 in Hyt as Hyx; eauto.
  assert (Z ⊂ X ∧ Y ⊂ Z). { andG. apply Hzt. apply Hyt. }
  destruct H as [Hzx Hyz]. assert (Ensemble Z ∧ Ensemble Y).
  { andG; eapply SubAxP; eauto. eapply IncTran; eauto. }
  destruct H as [Hze Hye]. split; intros Hsc;
  intros [A [B [Hae [Hbe [H Heq]]]]]; assert (A ⊂ Y ∧ B ⊂ Y);
  [subst; andG; intros x Hx; ens| |subst; andG; intros x Hx; ens|];
  destruct H0 as [Hay Hby]; apply Hsc; exists A, B; andG; auto;
  apply sep_F1 in H; [do 2 rewrite (subTop_T2c Z Y),
    (subTop_T2c X Z), AssocI, (CommuI Z Y), (IncI Y Z) in H; eens|
    do 2 rewrite (subTop_T2c X Y) in H; auto]; apply sep_F2; auto;
  try (rewrite (subTop_T2c X Y); tauto); rewrite (subTop_T2c Z Y),
    (subTop_T2c X Z), AssocI, (CommuI Z Y), (IncI Y Z); eens; tauto.
Qed.

Theorem scon_T2 : ∀ Y X cT, Ensemble X → SubTop Y X cT →
  disSubConnect Y cT ↔ ∃ A B, ⦿ A ∧ ⦿ B ∧ Separation A B X cT ∧ Y = A ⋃ B.
Proof.
  intros * Hxe Hst. split; intros [A [B [Hae [Hbe []]]]]; exists A, B; andG;
  auto; eapply separation_T; eauto; try apply H; subst; intros x Hx; ens.
Qed.

Theorem scon_T3 : ∀ Y X cT, Ensemble X → SubTop Y X cT →
  subConnect Y cT → ∀ A B, Separation A B X cT → Y ⊂ A ⋃ B → Y ⊂ A ∨ Y ⊂ B.
Proof.
  intros * Hxe Hyx Hsy * Hs Hsub. assert (Heq: A ∩ Y ⋃ B ∩ Y = Y).
  { rewrite <- DistribuI, CommuI; apply IncI; auto. }
  assert (Hd: A ∩ Y = ∅ ∨ B ∩ Y = ∅).
  { DC (A ∩ Y = ∅ ∨ B ∩ Y = ∅); auto. exfalso.
    apply not_or_and in H as [Ha Hb]. apply EmptyNE in Ha.
    apply EmptyNE in Hb. assert (disSubConnect Y cT).
    { apply (scon_T2 Y X cT); auto. exists (A∩Y), (B∩Y); andG; auto.
      split; andG; [intros x Hx|intros x Hx|]; inH; try apply Hyx; auto.
      assert ((A∩Y) ∩ Closure (B∩Y) X cT ⋃ (B∩Y) ∩ Closure (A∩Y) X cT ⊂
        (A∩Y) ∩ Closure B X cT ⋃ (B∩Y) ∩ Closure A X cT).
      { intros y Hy. unH; inH; [unG| apply UnionI']; inG; auto;
        eapply closure_F2; eauto; try apply Hs; intros z Hz; inH; auto. }
      AppE; [|exfalso0]. apply H in H0. destruct Hs as [_ [_ Hs]].
      rewrite (CommuI A Y), (CommuI B Y), AssocI, AssocI, <- DistribuLI, Hs,
        EmptyI in H0; auto. } apply Hsy, H. }
  orH; rewrite H in Heq; [rewrite CommuU in Heq|]; rewrite EmptyU in Heq;
  rewrite <- Heq; [right|left]; intros x Hx; inH; auto.
Qed.

Corollary scon_T3C1 : ∀ Y X cT, Ensemble X → SubTop Y X cT → subConnect Y cT →
  ∀ Z, SubTop Z X cT → Y ⊂ Z → Z ⊂ Closure Y X cT → subConnect Z cT.
Proof.
  intros * Hxe Hyx Hsy * HzX Hyz Hzc. DC (subConnect Z cT); auto.
  assert (Hzn: disSubConnect Z cT). unfold disSubConnect; apply NNPP, H.
  apply (scon_T2 Z X) in Hzn as [A [B [[x Ha] [[y Hb] [Hab Heq]]]]];
  auto. assert (A⊂X ∧ B⊂X). andG; apply Hab. destruct H0 as [Hax Hbx].
  assert (B = Z∩B ∧ A = Z∩A). { subst Z. andG; AppE; ens; inH; auto. }
  destruct H0 as [Hbz Haz]. clear H; pose proof Hab.
  apply sep_F1 in H as [Habc Hbac]. rewrite Heq in Hyz.
  apply (scon_T3 Y X) in Hab as [H|H]; auto;
  apply (closure_F2 Y _ X cT) in H; eauto.
  - assert (Z ⊂ Closure A X cT); eens. apply (InterRSub _ _ B) in H0.
    rewrite CommuI in Hbac. rewrite Hbac, <- Hbz in H0.
    assert (B = ∅). AppE; exfalso0. subst B; exfalso0.
  - assert (Z ⊂ Closure B X cT); eens. apply (InterRSub _ _ A) in H0.
    rewrite CommuI in Habc. rewrite Habc, <- Haz in H0.
    assert (A = ∅). AppE; exfalso0. subst A; exfalso0.
Qed.

Fact scon_T3C2 : ∀ A X cT, Ensemble X → SubTop A X cT →
  subConnect A cT → subConnect (Closure A X cT) cT.
Proof.
  intros * Hxe [Has Ht] Hac. assert (H: Closure A X cT ⊂ X).
  apply closureP; auto. assert (SubTop (Closure A X cT) X cT).
  split; andG; auto. eapply (scon_T3C1 A); eens. split; andG; auto.
  intros x Hx; unfold Closure; ens.
Qed.

Theorem scon_T4 : ∀ Y X cT, Ensemble X → SubTop Y X cT →
  ⦿ Interior Y X cT → Closure Y X cT ≠ X → Separation (Interior Y X cT)
  (X - (Closure Y X cT)) (X - (Bound Y X cT)) (cT|(X - (Bound Y X cT))).
Proof.
  intros * Hxe [Ht Hyx] Hye Hyn. assert (X - (Closure Y X cT) ⊂ X ∧
    X - (Closure Y X cT) ⊂ X - Bound Y X cT).
  { andG. apply SetminSubI. rewrite bound_F2; auto.
    apply SetminSub2; intros x Hx; ens. } destruct H as [Hbx Hby].
  assert (Interior Y X cT ⊂ X ∧ Interior Y X cT ⊂ X - Bound Y X cT).
  { andG. apply interiorP. rewrite bound_F3; auto. intros x Hx; smH; smG;
    auto. eapply closureP; revgoals; eauto. } destruct H as [Hax Hay].
  assert (Hst: SubTop (X - Bound Y X cT) X cT).
  { assert (X - Bound Y X cT ⊂ X). apply SetminSubI. split; andG; auto. }
  eapply separation_T, sep_F2; eauto.
  - rewrite (Re_bou_C1 (X - Closure Y X cT)), DistribuLI, <- bound_F1;
    try apply closureP; auto. apply two_union_Empty; andG.
    + rewrite bound_F2, TwoDMU; auto.
      AppE; [exfalso|exfalso0]. inH; smH; tauto.
    + rewrite bound_F3; auto. AppE; [exfalso|exfalso0].
      inH; smH. apply Re_bou_C4 in H0; auto.
  - rewrite (bound_F2 Y), (Re_bou_C1 (Interior Y X cT)), TwoDMU, DistribuLI;
    auto. apply two_union_Empty; andG; AppE; [exfalso|exfalso0|exfalso|exfalso0];
    inH; smH; auto. apply Re_bou_C3 in H0; auto.
Qed.

Corollary scon_T4C : ∀ Y X cT, Ensemble X → SubTop Y X cT →
  ⦿ Interior Y X cT → Closure Y X cT ≠ X → disSubConnect (X - (Bound Y X cT)) cT.
Proof.
  intros * Hxe [Ht Hyx] Hye Hyn. assert (Hbcx: X - Bound Y X cT ⊂ X).
  { intros x Hx; smH; auto. } assert (Hbe: Ensemble (X - Bound Y X cT)).
  { eapply SubAxP; eauto; intros x Hx; smH; auto. }
  assert (Hbt: Topology (X - Bound Y X cT) (cT | (X - Bound Y X cT))).
  { eapply resFam; revgoals; eauto. } apply nConnect_Td; auto.
  apply nConnect_Tc; eauto. assert (Hcx: Closure Y X cT ⊂ X).
  apply closureP; auto. assert (Hix: Interior Y X cT ⊂ X). apply interiorP.
  assert (Hbx: Bound Y X cT ⊂ X). apply boundP.
  exists (Interior Y X cT), (X - (Closure Y X cT)). andG; auto.
  - pose proof ProperSubE as [x []]. split; revgoals; eauto. exists x; ens.
  - assert (Interior Y X cT ∈ cT). apply interior_T2b; auto. AppCG; Ens.
    exists (Interior Y X cT); andG; auto. AppE; [|inH; auto]. inG; auto.
    smG; auto. rewrite bound_F3 in H0; auto. smH; auto.
  - assert (X - Closure Y X cT ∈ cT). apply closed_T, closure_F5; auto.
    AppCG; Ens. exists (X - Closure Y X cT). andG; auto. AppE; [|inH; auto].
    inG; auto. smH; smG; auto.
    rewrite interior_Tb, Re4_ClInBo in H1; auto. intro; ens.
  - AppE; [exfalso|exfalso0]. inH; smH. pose proof (interior_F2 Y X cT); auto.
  - apply subTop_T1; auto. split; auto.
Qed.