Require Import Classical.

(* symbol *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope.
Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∃ x .. y ']' , '/' P ']'") : type_scope.
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' 'λ' x .. y ']' , '/' t ']'").

Notation "x ∧ y" := (x /\ y)
  (at level 80, right associativity) : type_scope.
Notation "x ∨ y" := (x \/ y)
  (at level 85, right associativity) : type_scope.

Notation "x → y" := (x -> y)
  (at level 99, y at level 200, right associativity): type_scope.
Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.

Ltac PreandH := match goal with H : ?a ∧ ?b |- _ => destruct H end.
Ltac andH := repeat PreandH.

Ltac PreandG := match goal with |- ?a ∧ ?b => split end.
Ltac andG := repeat PreandG.

Ltac PreorH := match goal with H : ?a ∨ ?b |- _ => destruct H end.
Ltac orH := repeat PreorH.

(* Some logic *)
(* Axiom classic : ∀ P, P ∨ ~P. *)
Ltac DC P := destruct (classic P).

(* Logical property *)
Proposition NNPP : ∀ P, (~(~P) ↔ P).
Proof. intros; DC P; tauto. Qed.

Proposition inp : ∀ P Q : Prop, (P ↔ Q) → (~P → ~Q).
Proof. intros; intro. pose proof H1. elim H0. apply H; auto. Qed.

Proposition not_or_and : ∀ P Q, ~(P ∨ Q) → ~P ∧ ~Q.
Proof. intros. split; intro; apply H; auto. Qed.

(* Class *)
Parameter Class : Type.

(* Two primitive(undefined) constants *)
Parameter In : Class → Class → Prop.
Notation "a ∈ A" := (In a A)(at level 70).
Notation "a ∉ A" := (~(a ∈ A))(at level 70).

Parameter Classifier : ∀ P : Class → Prop, Class.
Notation "\{ P \}" := (Classifier P)(at level 0).

(* Set theory *)
Axiom ExtAx : ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.
Ltac AppE := apply ExtAx; split; intros.

Definition Ensemble x := ∃ y, x ∈ y.
Ltac Ens := unfold Ensemble; eauto.
Ltac AssE x := assert (Ensemble x); Ens.

Axiom ClaAx : ∀ x P, x ∈ \{P\} ↔ Ensemble x ∧ P x.
Ltac AppCG := apply ClaAx; split; eauto.
Ltac AppC H := apply ClaAx in H as [_ H]; eauto.

Definition NoEmpty A := ∃ x, x ∈ A.
Notation "⦿ A" := (NoEmpty A) (at level 45).

Definition Empty := \{ λ x, x ≠ x \}.
Notation " ∅ " := Empty.

Fact EmptyNI : ∀ x, x ∉ ∅.
Proof. intros x H. AppC H. Qed.
Hint Resolve EmptyNI : Ens_hint.
Ltac exfalso0 := exfalso; eapply EmptyNI; eauto.

Fact EmptyEq : ∀ x, x = ∅ ↔ ~ (⦿ x).
Proof.
  split; intros. subst x. intros [x H]. exfalso0.
  AppE. elim H. exists x0; auto. exfalso0.
Qed.

Fact EmptyNE : ∀ x, x ≠ ∅ ↔ ⦿ x.
Proof.
  intros. pose proof EmptyEq. split; intros.
  apply (inp _ (~(⦿ x))) in H; auto. apply -> NNPP in H; auto.
  intro; apply H in H0; auto.
Qed.

Definition μ := \{ λ x, x = x \}.
Fact UniveI : ∀ x, Ensemble x → x ∈ μ.
Proof. intros. AppCG. Qed.
Hint Immediate UniveI : Ens_hint.

Ltac ens := auto with Ens_hint.
Ltac eens := eauto with Ens_hint.

Definition Singleton x := \{ λ z, x ∈ μ → z = x \}.
Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Fact SingI : ∀ x, Ensemble x → ∀ y, y = x → y ∈ [x].
Proof. intros. subst. AppCG. Qed.
Hint Resolve SingI : Ens_hint.

Fact SingE : ∀ x, Ensemble x → ∀ y, y ∈ [x] → y = x.
Proof. intros. AppC H0; ens. Qed.
Ltac sing H := apply SingE in H; try (subst; eauto).

Definition Included A B := ∀ x, x ∈ A → x ∈ B.
Notation "A ⊂ B" := (Included A B)(at level 70).

Definition ProperSub A B := A ⊂ B ∧ A ≠ B.
Notation "A ⊊ B" := (ProperSub A B)(at level 70).

Axiom SubAx : ∀ x, Ensemble x → ∃ y, Ensemble y ∧ (∀z, z ⊂ x → z ∈ y).

Fact SubAxP : ∀ x, Ensemble x → ∀ z, z ⊂ x → Ensemble z.
Proof. intros. apply SubAx in H as [y []]. Ens. Qed.
Hint Resolve SubAxP : Ens_hint.

Fact EmptySub : ∀ A, ∅ ⊂ A.
Proof. intros A x Hx. exfalso0. Qed.

Fact IncRef : ∀ A, A ⊂ A.
Proof. intros * x; auto. Qed.

Fact IncAsym : ∀ A B, A ⊂ B → B ⊂ A → A = B.
Proof. intros. AppE; auto. Qed.

Fact IncTran : ∀ A B C, A ⊂ B → B ⊂ C → A ⊂ C.
Proof. intros * Ha Hb x Hx. auto. Qed.
Hint Resolve IncRef IncAsym IncTran : Ens_hint.

Fact ProperSubE : ∀ A B, A ⊊ B → ∃ x, x ∈ B ∧ x ∉ A.
Proof.
  intros * [Hs Hn]. assert (~(A ⊂ B ∧ B ⊂ A )).
  { intros []. assert (A = B); ens. }
  apply not_and_or in H as []. tauto.
  apply not_all_ex_not in H as [n H]. apply imply_to_and in H; eauto.
Qed.

Definition PowerSet X := \{λ A, A ⊂ X \}.
Notation " cP( X )" := (PowerSet X)(at level 9, right associativity).

Fact PowerI : ∀ X, Ensemble X → ∀ Y, Y ⊂ X → Y ∈ cP(X).
Proof. intros. AppCG. eens. Qed.

Fact PowerE : ∀ X Y, Y ∈ cP(X) → Y ⊂ X.
Proof. intros. AppC H. Qed.
Ltac pow H := apply PowerE in H; eauto.

Fact PowerEns : ∀ X, Ensemble X → Ensemble cP(X).
Proof.
  intros. apply SubAx in H as [B [Hbe Hb]].
  assert (cP(X) ⊂ B). { intros z Hz. pow Hz. } eens.
Qed.
Hint Resolve PowerI PowerEns : Ens_hint.

Fact UniveEns : ~Ensemble μ.
Proof.
  set \{λ x, x ∉ x\} as R. assert (~Ensemble R).
  { DC (R ∈ R). pose proof H; AppC H. intro; elim H; AppCG. }
  assert (R ⊂ μ). intros z Hz. AssE z; ens. intro; eens.
Qed.

Fact SingEns : ∀ x, Ensemble x → Ensemble [x].
Proof.
  intros. assert ([x] ⊂ cP(x)). { intros z Hz. sing Hz. ens. }
  apply PowerEns in H; eens.
Qed.

Fact SingEns' : ∀ x, Ensemble [x] → Ensemble x.
Proof.
  intros. DC (Ensemble x); auto. assert ([x] = μ).
  { apply (inp _ (x ∈ μ)) in H0. AppE; AssE x0. ens. AppCG.
    intro; tauto. split; ens. intro; Ens. }
  rewrite H1 in H. pose proof UniveEns. tauto.
Qed.
Hint Resolve SingEns SingEns' : Ens_hint.

Definition Union A B := \{λ x, x ∈ A ∨ x ∈ B\}.
Notation "A ⋃ B" := (Union A B)(at level 65, right associativity).

Fact UnionI : ∀ x A, x ∈ A → ∀ B, x ∈ A ⋃ B.
Proof. intros. AppCG; Ens. Qed.

Fact UnionI' : ∀ x B, x ∈ B → ∀ A, x ∈ A ⋃ B.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve UnionI UnionI' : Ens_hint.

Fact UnionE : ∀ x A B, x ∈ A ⋃ B → x ∈ A ∨ x ∈ B.
Proof. intros. AppC H. Qed.

Ltac PreunH := match goal with H : ?c ∈ ?a ⋃ ?b
  |- _ => apply UnionE in H as [] end.
Ltac unH := repeat PreunH.

Ltac PreunG := match goal with
  |- ?c ∈ ?a ⋃ ?b => apply UnionI end.
Ltac unG := repeat PreunG.

Fact UnionNE : ∀ x A B, x ∉ A ⋃ B → x ∉ A ∧ x ∉ B.
Proof. intros. split; intro; ens. Qed.

Axiom UnionAx : ∀ x y, Ensemble x → Ensemble y → Ensemble (x ⋃ y).

Fact UnionEns : ∀ x y, Ensemble (x ⋃ y) → Ensemble x ∧ Ensemble y.
Proof.
  intros. assert (x ⊂ x ⋃ y ∧ y ⊂ x ⋃ y).
  split; intros z Hz; ens. andH. split; eens.
Qed.

Definition Inter A B := \{λ x, x ∈ A ∧ x ∈ B\}.
Notation "A ∩ B" := (Inter A B)(at level 60, right associativity).

Fact InterI : ∀ x A B, x ∈ A → x ∈ B → x ∈ A ∩ B.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve InterI : Ens_hint.

Fact InterE : ∀ x A B, x ∈ A ∩ B → x ∈ A ∧ x ∈ B.
Proof. intros. AppC H. Qed.

Ltac PreinH := match goal with H : ?c ∈ ?a ∩ ?b
  |- _ => apply InterE in H as [] end.
Ltac inH := repeat PreinH.

Ltac PreinG := match goal with
  |- ?c ∈ ?a ∩ ?b => apply InterI end.
Ltac inG := repeat PreinG.

Fact InterEns : ∀ x y, Ensemble x → Ensemble y → Ensemble (x ∩ y).
Proof.
  intros. assert (x ∩ y ⊂ x). intros z Hz. AppC Hz; tauto. eens.
Qed.

(* Axiom RegAx : ∀ x, x ≠ ∅ → ∃ y, y ∈ x ∧ x ∩ y = ∅. *)
Definition Setmin A B := \{λ x, x ∈ A ∧ x ∉ B\}.
Notation "A - B" := (Setmin A B).

Fact SetminI : ∀ x A B, x ∈ A → x ∉ B → x ∈ A - B.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve SetminI : Ens_hint.

Fact SetminE : ∀ x A B, x ∈ A - B → x ∈ A ∧ x ∉ B.
Proof. intros. AppC H. Qed.

Ltac PresmH := match goal with H : ?c ∈ ?a - ?b
  |- _ => apply SetminE in H as [] end.
Ltac smH := repeat PresmH.

Ltac PresmG := match goal with
  |- ?c ∈ ?a - ?b => apply SetminI end.
Ltac smG := repeat PresmG.

Fact SetminIE : ∀ A B X, A ⊂ X → B ⊂ X → A - B = A ∩ (X - B).
Proof. intros. AppE. smH; ens. inH; smH; ens. Qed.

Fact SetminNI : ∀ x A X, x ∈ A → x ∉ X - A.
Proof. intros * Hx Hs. smH; tauto. Qed.

Fact SetminId : ∀ X, X - X = ∅.
Proof. intro. AppE. smH; tauto. exfalso0. Qed.

Fact SetminEm : ∀ X, X - ∅ = X.
Proof. intro. AppE. smH; tauto. ens. Qed.

Fact SetminEq : ∀ A B X, A = B → X - A = X - B.
Proof. intros. subst. auto. Qed.

Fact SetminSubI : ∀ A X, X - A ⊂ X.
Proof. intros * x Hx. smH; tauto. Qed.

Fact SetminEns : ∀ x, Ensemble x → ∀ y, Ensemble (x - y).
Proof. intros. pose proof (SetminSubI y x). eens. Qed.
Hint Resolve UnionAx InterEns SetminEns : Ens_hint.

Fact UnionSetmin: ∀ A B, A ⋃ (B - A) = A ⋃ B.
Proof. intros. AppE. unH; ens. smH; ens. unH; ens. DC (x ∈ A); ens. Qed.

Fact InterSetmin : ∀ A B X, B ⊂ X → B ∩ X - A = ∅ → B ⊂ A.
Proof.
  intros * Hs Hp z Hz. assert (z ∉ X - A).
  { intro. assert (z ∈ B ∩ X - A); ens. rewrite Hp in H0; exfalso0. }
  DC(z ∈ A); auto. elim H; ens.
Qed.

Fact InterEqEmI : ∀ x U A, Ensemble x →
  U ∩ A - [x] = ∅ → x ∉ A → U ∩ A = ∅.
Proof.
  intros. assert (A - [x] = A). { AppE. smH; tauto.
  assert (x0 ∉ [x]). intro; sing H3. ens. } rewrite H2 in H0; auto.
Qed.

Fact InterEqEmE : ∀ x U A, U ∩ A = ∅ → U ∩ A - [x] = ∅.
Proof.
  intros. AppE; [|exfalso0]. inH. smH.
  assert (x0 ∈ U ∩ A); ens. rewrite H in H3; exfalso0.
Qed.

Fact SetminSub : ∀ A B X, A ⊂ X → A - B ⊂ X.
Proof. intros * Ha z Hz. smH; auto. Qed.

Fact SetminSub1 : ∀ A B C, A ⊂ B → A - C ⊂ B - C.
Proof. intros * Hab z Hz. smH; ens. Qed.

Fact SetminSub2 : ∀ A B X, A ⊂ B → X - B ⊂ X - A.
Proof. intros * Hab z Hz. smH; ens. Qed.

Fact SetminInter : ∀ A B X, A ⊂ X → A - B = A ∩ X - B.
Proof. intros. AppE. smH; ens. inH; smH; ens. Qed.

Fact InterRSub : ∀ A B X, A ⊂ B → A ∩ X ⊂ B ∩ X.
Proof. intros * Hab z Hz. inH; ens. Qed.

Fact IdemU : ∀ A, A ⋃ A = A.
Proof. intros. AppE. unH; auto. ens. Qed.

Fact IdemI : ∀ A, A ∩ A = A.
Proof. intros. AppE; inH; ens. Qed.

Fact CommuU : ∀ A B, A ⋃ B = B ⋃ A.
Proof. intros. AppE; unH; ens. Qed.

Fact CommuI : ∀ A B, A ∩ B = B ∩ A.
Proof. intros. AppE; inH; ens. Qed.

Fact AssocU : ∀ A B C, (A ⋃ B) ⋃ C = A ⋃ (B ⋃ C).
Proof. intros. AppE; unH; ens. Qed.

Fact AssocI : ∀ A B C, (A ∩ B) ∩ C = A ∩ (B ∩ C).
Proof. intros. AppE; inH; ens. Qed.

Fact DistribuU : ∀ A B C, (A ∩ B) ⋃ C = (A ⋃ C) ∩ (B ⋃ C).
Proof. intros. AppE. unH; inH; ens. inH; unH; ens. Qed.

Fact DistribuI : ∀ A B C, (A ⋃ B) ∩ C = (A ∩ C) ⋃ (B ∩ C).
Proof. intros. AppE. inH; unH; ens. unH; inH; ens. Qed.

Fact TwoDMU : ∀ A B C, A - (B ⋃ C) = (A - B) ∩ (A - C).
Proof.
  intros. AppE. smH; inG; ens. inH; smH. smG; auto. intro; unH; auto.
Qed.

Fact TwoDMI : ∀ A B C, A - (B ∩ C) = (A - B) ⋃ (A - C).
Proof.
  intros. AppE. smH; DC (x ∈ C); ens. unG; ens.
  unH; smH; smG; auto; intro; inH; auto.
Qed.

Fact DistribuLI : ∀ A B C, A ∩ (B ⋃ C) = A ∩ B ⋃ A ∩ C.
Proof. intros. rewrite CommuI, DistribuI, CommuI, (CommuI A C); auto. Qed.

Fact DistribuLU : ∀ A B C, A ⋃ (B ∩ C) = (A ⋃ B) ∩ (A ⋃ C).
Proof. intros. rewrite CommuU, DistribuU, CommuU, (CommuU C A); auto. Qed.

Fact EmptyU : ∀ A, A ⋃ ∅ = A.
Proof. intros. AppE. unH; auto. exfalso0. ens. Qed.

Fact EmptyI : ∀ A, A ∩ ∅ = ∅.
Proof. intros. AppE. inH; auto. exfalso0. Qed.

Fact IncU : ∀ A X, A ⊂ X → A ⋃ X = X.
Proof. intros. AppE. unH; auto. ens. Qed.

Fact IncI : ∀ A X, A ⊂ X → A ∩ X = A.
Proof. intros. AppE. inH; auto. ens. Qed.

Fact ComUn : ∀ A X, A ⊂ X → A ⋃ X - A = X.
Proof. intros. AppE. unH; auto. smH; auto. DC (x ∈ A); ens. Qed.

Fact ComIn : ∀ A X, A ⊂ X → A ∩ X - A = ∅.
Proof. intros. AppE; [|exfalso0]. inH; smH; tauto. Qed.

Fact UnionCompl : ∀ A B X, A ⊂ X → B ⊂ X →
  X - (A ⋃ B) = X - A ∩ X - B.
Proof. intros. rewrite TwoDMU; auto. Qed.

Fact InterCompl : ∀ A B X, A ⊂ X → B ⊂ X →
  X - (A ∩ B) = X - A ⋃ X - B.
Proof. intros. rewrite TwoDMI; auto. Qed.

Fact TwoCompl : ∀ A X, A ⊂ X → X - (X - A) = A.
Proof.
  intros. AppE. smH. DC (x ∈ A); auto. elim H1; ens.
  smG; auto. intro; smH; auto.
Qed.

Fact DisLII : ∀ A B C, (A ∩ B) ∩ C = (A ∩ C) ∩ (B ∩ C).
Proof. intros. AppE; inH; ens. Qed.

Fact two_union_Empty : ∀ A B, A ⋃ B = ∅ ↔ A = ∅ ∧ B = ∅.
Proof.
  split; intros. andG; AppE; try exfalso0; rewrite <- H; eens.
  andH; subst. rewrite EmptyU; auto.
Qed.

Fact two_inter_Empty : ∀ A B X, A ⊂ X → B ⊂ X →
  A ∩ B = ∅ → A ⋃ B = X → A = X - B.
Proof.
  intros. AppE; [DC (x ∈ B)|DC (x ∈ A)]; ens. assert (x ∈ A ∩ B); ens.
  rewrite H1 in H5; exfalso0. exfalso; smH; rewrite <- H2 in H3; unH; ens.
Qed.

Fact unEq_inEm_idEq : ∀ A B C, A ⋃ B = A ⋃ C → A ∩ B = ∅ → A ∩ C = ∅ → B = C.
Proof.
  intros. assert ((A⋃B)∩C = (A⋃C)∩C ∧ (A⋃B)∩B = (A⋃C)∩B). andG; rewrite H;
  auto. destruct H2 as [Hc Hb]. rewrite DistribuI, DistribuI, H1, IdemI,
    CommuU, EmptyU, CommuU, EmptyU, CommuI in Hc. rewrite DistribuI,
    DistribuI, H0, IdemI, CommuU, EmptyU, CommuU, EmptyU, Hc in Hb; auto.
Qed.

Definition EleU x := \{λ z, ∃ y, z ∈ y ∧ y ∈ x\}.
Notation "∪ x" := (EleU x)(at level 66).

Fact EleUI : ∀ x y z, x ∈ y → y ∈ z → x ∈ ∪z.
Proof. intros. AppCG; Ens. Qed.
Hint Resolve EleUI : Ens_hint.

Fact EleUE : ∀ x z, x ∈ ∪z → ∃ y, x ∈ y ∧ y ∈ z.
Proof. intros. AppC H. Qed.
Ltac eleU H := apply EleUE in H as [? []]; eauto.

Axiom EleUAx : ∀ x, Ensemble x → Ensemble (∪x).
Hint Resolve EleUAx : Ens_hint.

Axiom InfAx : ∃ y, Ensemble y ∧ ∅ ∈ y ∧ (∀ x, x ∈ y → (x ⋃ [x]) ∈ y).

Fact EmptyEns : Ensemble ∅.
Proof. destruct InfAx as [x [_ [He _]]]; Ens. Qed.
Hint Resolve EmptyEns : Ens_hint.

Fact EleUEm : ∪∅ = ∅.
Proof. AppE; [|exfalso0]. eleU H; exfalso0. Qed.

Fact EleUSin : ∀ x, Ensemble x → ∪[x] = x.
Proof. intros. AppE. eleU H0; sing H1. eens. Qed.

Fact EleUEleSub : ∀ A B, A ∈ B → A ⊂ ∪B.
Proof. intros * Ha x Hx. eens. Qed.

Fact EleUSub: ∀ A B, A ⊂ B → ∪A ⊂ ∪B.
Proof. intros * H x Hx. eleU Hx. eens. Qed.

Fact EleUTwoUn : ∀ a b, ∪(a ⋃ b) = (∪a) ⋃ (∪b).
Proof. intros. AppE. eleU H; unH; eens. unH; eleU H; eens. Qed.

Fact IntSinEm : ∀ A B C, Ensemble C →
  A ∈ [C] ⋃ [∅] → B ∈ [C] ⋃ [∅] → A ∩ B ∈ [C] ⋃ [∅].
Proof.
  intros. unH; sing H0; sing H1; ens; try (rewrite EmptyI); ens;
  [rewrite IdemI|rewrite CommuI, EmptyI]; ens.
Qed.

Fact EleUSinEm : ∀ a T, Ensemble a → T ⊂ [a] ⋃ [∅] → ∪T ∈ [a] ⋃ [∅].
Proof.
  intros * Hae Ht. assert (Hte : Ensemble T).
  { assert (Ensemble ([a] ⋃ [∅])). ens. eens. }
  assert (T ∈ cP([a] ⋃ [∅])). eens.
  assert (∀ c d, Ensemble c → Ensemble d → cP([c] ⋃ [d]) =
    \{ λ Z, Z = ∅ ∨ Z = [c] ∨ Z = [d] ∨ Z = [c] ⋃ [d] \}).
  { intros. AppE.
    - AppCG; Ens. pow H2. DC (c ∈ x); DC (d ∈ x);
      [right; right; right|right; left|right; right; left|left].
      + apply IncAsym; auto; intros z Hz; unH; sing H5.
      + AppE; [|sing H5]; AppCG; Ens;
        assert (H5' := H5); apply H2 in H5; unH; sing H5; tauto.
      + AppE; [|sing H5]. AppCG; Ens.
        assert (H5' := H5); apply H2 in H5; unH; sing H5; tauto.
      + AppE; [|exfalso0].
        assert (H5' := H5); apply H2 in H5; unH; sing H5; tauto.
    - AppCG; Ens. intros z Hz. AppC H2.
      orH; subst; [exfalso0| | |auto]; ens. }
  rewrite H0 in H; ens. AppC H; orH; subst; try rewrite EleUSin; eens.
  rewrite EleUEm; ens. assert (∪[a]⋃[∅] = a).
  { rewrite EleUTwoUn, EleUSin, EleUSin, EmptyU; ens. }
  rewrite H; ens.
Qed.

Definition EleI x := \{λ z, ∀ y, y ∈ x → z ∈ y\}.
Notation "⋂ x" := (EleI x)(at level 66).

Fact EleISin : ∀ x, Ensemble x → ⋂[x] = x.
Proof.
  intros. AppE. AppC H0; apply H0; ens. AppCG; Ens. intros; sing H1.
Qed.
Hint Immediate EleUSin EleISin : Ens_hint.

Fact EleIEle : ∀ A B, A ∈ B → ⋂B ⊂ A.
Proof. intros. intros x Hx. AppC Hx. Qed.

Fact EleIEns : ∀ cA, cA ≠ ∅ → Ensemble (⋂cA).
Proof.
  intros. apply EmptyNE in H as [A]. apply EleIEle in H as H'.
  assert (Ensemble A). Ens. eens.
Qed.
Hint Resolve EleIEns : Ens_hint.


Definition Unorder x y := [x] ⋃ [y].
Notation "[ x | y ] " := (Unorder x y) (at level 0).

Fact UnordIE : ∀ x y, Ensemble x → Ensemble y →
  ∀ z, z ∈ [x|y] ↔ z = x ∨ z = y.
Proof.
  intros. unfold Unorder. split; intros. unH; sing H1. orH; subst; ens.
Qed.

Fact UnordEns : ∀ x y, Ensemble x → Ensemble y → Ensemble [x|y].
Proof. intros. unfold Unorder. ens. Qed.
Hint Resolve UnordEns : Ens_hint.

Fact unord1 : ∀ x y, Ensemble x → Ensemble y → ∪[x|y] = x ⋃ y.
Proof.
  intros. unfold Unorder. AppE. eleU H1; unH; sing H2; ens.
  unH; eapply EleUI; eauto; ens.
Qed.

Fact unord2 : ∀ x y, Ensemble x → Ensemble y → ⋂[x|y] = x ∩ y.
Proof.
  intros. unfold Unorder. AppE. AppC H1; ens.
  inH. AppCG; Ens. intros. unH; sing H3.
Qed.

Definition Order x y := [ [x] | [x | y] ].
Notation "[ x , y , .. , z ]" :=
  (Order .. (Order x y ) .. z ) (z at level 69).

Fact OrdEns : ∀ x y, Ensemble x → Ensemble y → Ensemble [x,y].
Proof. intros. unfold Order. ens. Qed.

Fact OrdEns0 : ∀ x y, Ensemble [x,y] → Ensemble x ∧ Ensemble y.
Proof.
  intros. apply UnionEns in H as [].
  apply SingEns', UnionEns in H0 as []; ens.
Qed.

Fact OrdEns1 : ∀ x y, Ensemble [x,y] → Ensemble x.
Proof. intros. apply OrdEns0 in H; tauto. Qed.

Fact OrdEns2 : ∀ x y, Ensemble [x,y] → Ensemble y.
Proof. intros. apply OrdEns0 in H; tauto. Qed.

Fact OrdEns3 : ∀ x y, Ensemble [x,y] → Ensemble [y,x].
Proof. intros. apply OrdEns0 in H as []. apply OrdEns; auto. Qed.
Hint Resolve OrdEns OrdEns3 : Ens_hint.

Ltac orde1 := match goal with H : Ensemble [?x,?y]
  |- Ensemble ?x => eapply OrdEns1; eauto end.
Ltac orde2 := match goal with H : Ensemble [?x,?y]
  |- Ensemble ?y => eapply OrdEns2; eauto end.
Ltac orde := try orde1; try orde2.

Fact ord1 : ∀ x y, Ensemble x → Ensemble y → ∪[x,y] = [x|y].
Proof.
  intros. unfold Order. rewrite unord1; ens.
  AppE; ens. unH; unfold Unorder; ens.
Qed.

Fact ord2 : ∀ x y, Ensemble x → Ensemble y → ⋂[x,y] = [x].
Proof.
  intros. unfold Order. rewrite unord2; ens.
  AppE. inH; auto. unfold Unorder; ens.
Qed.

Fact ord3 : ∀ x y, Ensemble x → Ensemble y → ∪(⋂[x,y]) = x.
Proof. intros. rewrite ord2; ens. Qed.

Fact ord4 : ∀ x y, Ensemble x → Ensemble y → ⋂(⋂[x,y]) = x.
Proof. intros. rewrite ord2; ens. Qed.

Fact ord5 : ∀ x y, Ensemble x → Ensemble y → ∪(∪[x,y]) = x ⋃ y.
Proof. intros. rewrite ord1, unord1; ens. Qed.

Fact ord6 : ∀ x y, Ensemble x → Ensemble y → ⋂(∪[x,y]) = x ∩ y.
Proof. intros. rewrite ord1, unord2; ens. Qed.

Definition π1 z := ⋂⋂z.
Definition π2 z := (⋂∪z)⋃(∪∪z)-(∪⋂z).

Fact ordFis : ∀ x y, Ensemble x → Ensemble y → π1 [x,y] = x.
Proof. intros. apply ord4; ens. Qed.

Fact ordSec : ∀ x y, Ensemble x → Ensemble y → π2 [x,y] = y.
Proof.
  intros. unfold π2. rewrite ord6, ord5, ord3; ens.
  assert ((x ⋃ y) - x = y - x). { AppE; smH; ens. unH. tauto. ens. }
  rewrite H1, CommuI. AppE; [|DC (x0 ∈ x); ens].
  unH. inH; auto. smH; auto.
Qed.

Fact ordEq : ∀ x y a b, Ensemble x → Ensemble y →
  [x,y] = [a,b] ↔ x = a ∧ y = b.
Proof.
  split; intros; [|destruct H1; subst; auto]. assert (Ensemble [x,y]).
  eens. rewrite H1 in H2. apply OrdEns0 in H2 as [].
  rewrite <- (ordFis x y), H1, <- (ordSec x y), H1, ordFis, ordSec; auto.
Qed.

Notation " \{\ P \}\ " :=
  \{λ z, ∃ x y, z = [x,y] ∧ P x y \}(at level 0).
Ltac PP H a b := apply ClaAx in H as [_ [a [b [? H]]]]; subst; eauto.

Fact ClaAx' : ∀ x y P, [x,y] ∈ \{\P\}\ ↔ Ensemble [x,y] ∧ (P x y).
Proof.
  split; intros. AssE [x,y]. PP H a b. apply ordEq in H1 as []; orde.
  subst; auto. destruct H; AppCG; eauto.
Qed.
Ltac AppCG' := apply ClaAx'; split; eauto.
Ltac AppC' H := apply ClaAx' in H as [_ H]; eauto.

Definition Cartesian X Y := \{\ λ x y, x ∈ X ∧ y ∈ Y\}\.
Notation " X × Y " := (Cartesian X Y)(at level 2, right associativity).

Fact CProdI : ∀ A B a b, a ∈ A → b ∈ B → [a,b] ∈ A × B.
Proof. intros * Ha Hb. AppCG'. apply OrdEns; Ens. Qed.
Hint Resolve CProdI : Ens_hint.

Fact CProdE : ∀ A B a b, [a,b] ∈ A × B → a ∈ A ∧ b ∈ B.
Proof. intros. AppC' H. Qed.
Ltac cprod H := apply CProdE in H as []; eauto.

Definition relation R := ∀ z, z ∈ R → ∃ x y, z = [x,y].
Definition Relation R X Y := R ⊂ X × Y.

Definition Range R := \{λ y, ∃ x, [x,y] ∈ R\}.
Notation " ran( R )" := (Range R)(at level 5).

Fact ranI : ∀ R x y, [x,y] ∈ R → y ∈ ran(R).
Proof. intros. AssE [x,y]. AppCG; orde. Qed.
Hint Resolve ranI : Ens_hint.

Fact ranE : ∀ R y, y ∈ ran(R) → ∃ x, [x,y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac ran H := apply ranE in H as [?]; eauto.

Definition Domain R := \{λ x, ∃ y, [x,y] ∈ R\}.
Notation " dom( R )" := (Domain R)(at level 5).

Fact domI : ∀ R x y, [x,y] ∈ R → x ∈ dom(R).
Proof. intros. AssE [x,y]. AppCG; orde. Qed.
Hint Resolve domI : Ens_hint.

Fact domE : ∀ R x, x ∈ dom(R) → ∃ y, [x, y] ∈ R.
Proof. intros. AppC H. Qed.
Ltac dom H := apply domE in H as [?]; eauto.

Definition Function f :=
  relation f ∧ ∀ x y z, [x,y] ∈ f ∧ [x,z] ∈ f → y = z.

Axiom RepAx : ∀ f, Function f → Ensemble dom(f) → Ensemble ran(f).
Hint Resolve RepAx : Ens_hint.

Fact CProdEns0 : ∀ u y, Ensemble u → Ensemble y → Ensemble ([u] × y).
Proof.
  intros. set \{\λ w z, w ∈ y ∧ z = [u,w]\}\ as f.
  assert (Function f ∧ dom(f) = y ∧ ran(f) = [u] × y).
  { andG. split. intros z Hz; PP Hz a b. intros * [].
    AppC' H1; AppC' H2; andH. subst; auto.
    - AppE. dom H1; AppC' H1; tauto. AssE x; eapply domI; AppCG; eens.
    - AppE. ran H1; AppC' H1; andH. subst; ens. PP H1 a b; andH.
      sing H1. AssE b. AppCG; ens. exists b. AppCG'; eens. }
  andH. rewrite <- H2 in H0. rewrite <- H3. ens.
Qed.

Fact CProdEns : ∀ x y, Ensemble x → Ensemble y → Ensemble x × y.
Proof.
  intros. set \{\λ u z, u ∈ x ∧ z = [u] × y\}\ as f.
  assert (Function f ∧ dom(f) = x ∧
    ran(f) = \{λ z, ∃ u, u ∈ x ∧ z = [u] × y\}).
  { repeat split. intros z Hz; PP Hz a b.
    intros * []; AppC' H1; AppC' H2; andH. subst; auto.
    - AppE. dom H1. AppC' H1; tauto. AssE x0; eapply domI; AppCG'.
      apply OrdEns; auto. apply CProdEns0; auto.
    - AppE. ran H1; AppC' H1; andH; subst. AssE x1; AppCG.
      apply CProdEns0; auto. AppC H1. destruct H1; andH. subst. AssE x1.
      eapply ranI; AppCG. apply OrdEns; auto. apply CProdEns0; auto. }
  assert (∪ran(f) = x × y).
  { AppE. eleU H2; ran H3; AppC' H3; destruct H3. AssE x2; subst.
    PP H2 a b; destruct H2; sing H2; ens. pose proof H2. PP H2 a b; andH.
    AssE a; AppCG; Ens. exists [a] × y. split; ens. eapply ranI.
    AppCG'; eauto; ens. apply OrdEns; auto. apply CProdEns0; auto. }
  andH. rewrite <- H2. rewrite <- H3 in H. ens.
Qed.
Hint Resolve CProdEns : Ens_hint.

Definition Mapping F X Y := Relation F X Y ∧
  (∀ x, x ∈ X → (∃ y, [x,y] ∈ F)) ∧
  (∀ x y1 y2, [x,y1] ∈ F → [x,y2] ∈ F → y1 = y2 ).

Definition Value F x := ⋂\{λ y, [x,y] ∈ F\}.
Notation "F [ x ]" := (Value F x)(at level 5).

Fact ValueEns :∀ f x, x ∈ dom(f) → Ensemble f[x].
Proof.
  intros. unfold Value. assert (\{λ y, [x,y] ∈ f\} ≠ ∅).
  { dom H. apply EmptyNE. exists x0. AssE [x,x0]. AppCG; orde. } ens.
Qed.

Fact ValueP : ∀ f X Y, Mapping f X Y → ∀ x, x ∈ X → [x,f[x]] ∈ f.
Proof.
  intros * [Hr [He Hu]] * Hx. apply He in Hx as [y]. assert (y = f[x]).
  { AssE [x,y]. AppE. AppCG; Ens. intros; AppC H2. assert (y = y0).
    eapply Hu; eauto. subst; auto. AppC H1; apply H1; AppCG; orde. }
  subst; auto.
Qed.
Hint Resolve ValueEns ValueP : Ens_hint.

Fact ValueP1 : ∀ f X Y, Mapping f X Y → ∀ x, x ∈ X → f[x] ∈ Y.
Proof. intros. assert ([x,f[x]] ∈ f). eens. apply H in H1. cprod H1. Qed.

Fact ValueP2 : ∀ f X Y,
  Mapping f X Y → ∀ x y, x ∈ X → [x,y] ∈ f → y = f[x].
Proof. intros. eapply H; eens. Qed.
Hint Resolve ValueP1 ValueP2 : Ens_hint.

Fact Map_dom : ∀ F X Y, Mapping F X Y → dom(F) = X.
Proof. intros. AppE; eens. dom H0. apply H in H0. cprod H0. Qed.

Definition Restriction f A := \{\λ a b, [a,b] ∈ f ∧ a ∈ A\}\.
Notation "f ↾ A" := (Restriction f A)(at level 30).

Fact RestrI : ∀ f a b A, [a,b] ∈ f → a ∈ A → [a,b] ∈ f↾A.
Proof. intros. AppCG'; Ens. Qed.
Hint Resolve RestrI : Ens_hint.

Fact RestrE : ∀ f A a b, [a,b] ∈ f↾A → [a,b] ∈ f ∧ a ∈ A.
Proof. intros. AppC' H. Qed.
Ltac restr H := apply RestrE in H as []; eauto.

Fact RestrDom : ∀ F A, dom(F↾A) ⊂ dom(F).
Proof. intros * x H. dom H. restr H. eens. Qed.

Fact RestrM : ∀ f X Y, Mapping f X Y → ∀ A, A ⊂ X → Mapping (f↾A) A Y.
Proof.
  intros. split; [|split; intros; eens]. intros z Hz; PP Hz a b; andH.
  apply H in H1; cprod H1; ens. restr H1; restr H2; eapply H; eauto.
Qed.

Fact RestrValue : ∀ f X Y, Mapping f X Y → ∀ A, A ⊂ X →
  ∀ a, a ∈ A → f[a] = (f↾A)[a].
Proof.
  intros. AppE; AppCG; Ens; AppC H2; intros; AssE y;
  AppC H3; [restr H3|]; apply H2; AppCG; ens.
Qed.

Definition neSub X := cP(X) - [∅].
Notation " X ^ " := (neSub X) (at level 0).

Fact neSubEm : ∅^ = ∅.
Proof.
  unfold neSub. AppE; [|exfalso0]. smH. pow H. assert (x ≠ ∅).
  { intro. subst. ens. } elim H1. AppE. auto. exfalso0.
Qed.

Definition ChoiceF ε X := Mapping ε X^ X ∧ ∀ A, A ∈ X^ → ε[A] ∈ A.

Axiom ChoiceAx : ∀ X, ∃ ε, ChoiceF ε X.

Fact ChoAx : ∀ cA, ∅ ∉ cA →
  (∃ ν, Mapping ν cA (∪cA) ∧ (∀ A, A ∈ cA → ν[A] ∈ A )).
Proof.
  intros * Hn. set (X := ∪cA). assert (cA ⊂ X^).
  { intros A Ha. AppCG; andG; Ens. AppCG; Ens.
    intros x Hx; AppCG; Ens. intro; sing H; ens. }
  pose proof (ChoiceAx X) as [ε [Hf Hp]]. set (ν := ε↾cA).
  exists ν. andG. eapply RestrM; eauto. intros. assert (ε[A] = ν[A]).
  eapply RestrValue; eauto. rewrite <- H1. apply Hp. auto.
Qed.

Fact ChoAx1 : ∀ U P, Ensemble P → (∀ x, x ∈ U → ∃ y, [x,y] ∈ P) →
  ∃ f, Mapping f U \{λ z, ∃ x, x ∈ U ∧ [x,z] ∈ P\} ∧
  (∀ x, x ∈ U → [x,f[x]] ∈ P).
Proof.
  intros * Hpe Hp. DC (U = ∅).
  - subst. set (\{\λ u v, u ∈ ∅\}\) as f. exists f. andG; [split|].
    intros z Hz; PP Hz a b; exfalso0. andG. intros; exfalso0.
    intros; AppC' H0; exfalso0. intros; exfalso0.
  - set (\{λ Y, ∃ x, x ∈ U ∧ Y = \{λ y, [x,y] ∈ P\} \}) as cA.
    assert (Hp1 : ∅ ∉ cA). { intro He. AppC He; destruct He as
      [x [Hx Hm]], (Hp _ Hx) as [y Hxy].
    AssE [x,y]; apply OrdEns2 in H0. assert (y ∈ ∅).
    rewrite Hm; AppCG. exfalso0. }
    assert (Hxf : ∀ x, x ∈ U → \{λ y, [x,y] ∈ P\} ∈ cA).
    { intros. AppCG. set \{\ λ a b, ∃ x, [x,b] ∈ P ∧ a = [x,b]\}\ as f.
      assert (\{λ y, [x, y] ∈ P \} ⊂ ran(f)).
      { intros y Hy. AssE y; AppC Hy. AppCG. exists ([x,y]).
        AppCG'. apply OrdEns; Ens. }
      eapply SubAxP; revgoals; eauto. apply RepAx.
      - split. intros z Hz; PP Hz a b. intros * []; AppC' H2; AppC' H3.
        destruct H2, H3; andH. subst. AssE [x1,y].
        apply OrdEns0 in H5; andH. apply ordEq in H4; tauto.
      - assert (dom(f) ⊂ P). intros z Hz. dom Hz. AppC' H2.
        destruct H2; andH. subst; auto. eens. }
    destruct (ChoAx _ Hp1) as [c [Hc Hcp]]. set \{\λ u v, u ∈ U ∧
      v = c[\{λ y, [u,y] ∈ P\}]\}\ as ν. exists ν. andG; [split; andG|].
    + intros z Hz. AssE z; PP Hz u v; andH. AppCG'. apply OrdEns2 in H0.
      andG; auto. AppCG. exists u. andG; auto.
      apply Hxf, Hcp in H1. rewrite <- H2 in H1. AppC H1.
    + intros. AssE x. exists c[\{λ y, [x,y] ∈ P\}]. AppCG'. apply OrdEns;
      auto. apply ValueEns. erewrite Map_dom; eauto.
    + intros. AppC' H0; AppC' H1; andH. subst; auto.
    + intros * Hx. pose proof Hx as Hx'; apply Hxf, Hcp in Hx. AppC Hx.
      assert (c[\{λ y, [x,y] ∈ P\}] = ν [x]).
      { AppE; AppCG; Ens; AppC H0; intros * Hy; apply H0; AppCG; Ens.
        - AppC Hy. AppC' Hy; andH. subst y. eapply ValueP; eauto.
        - AppCG'; andG; auto. apply OrdEns; Ens. AppC Hy.
          eapply ValueP2; eauto. } rewrite <- H0; auto.
Qed.
