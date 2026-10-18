/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.LeftFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.Monoidal.Braided.PushoutObjObj
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Left anodyne extensions and pushout-products, left fibrations and pullbacks

This file mirrors, for *left* anodyne extensions and *left* fibrations
(`SimplicialHomotopy.Fibration.LeftFibrations`), what Mathlib does for inner anodyne
extensions in
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic`
(`Subcomplex.Pairing.innerAnodyneExtensions`) and
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`.

* `SSet.Subcomplex.Pairing.IsLeft`, `SSet.Subcomplex.PairingCore.IsLeft` : a (Moss) pairing
  only involves *left* horns (`index ≠ Fin.last _`); an inner pairing is a left pairing.
* `SSet.Subcomplex.Pairing.leftAnodyneExtensions` : a regular left pairing on `A`
  exhibits `A.ι` as a left anodyne extension.
* `SSet.prodStdSimplex.leftAnodyneExtensions_unionProd_ι` :
  `(Λ[m + 1, k] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ↪ Δ[m + 1] ⊗ Δ[n]` is left anodyne for
  `k < Fin.last (m + 1)`.
* `SSet.leftFibration_pullbackObjObjπ` : if `i` is a monomorphism and `p` a left
  fibration then the induced map `Y₁ ⟶[SSet] E ⟶ (X₁ ⟶[SSet] E) ×_{X₁ ⟶[SSet] B} (Y₁ ⟶[SSet] B)`
  is a left fibration ([Lur09, Corollary 2.1.2.9]).
* `SSet.leftAnodyneExtensions_pushoutObjObjι`, `…ι'`, `SSet.leftAnodyneExtensions_unionProd_ι`,
  `…ι'` : the pushout-product of a monomorphism and a left anodyne extension is left
  anodyne ([Lur09, Corollary 2.1.2.7]).
* `SSet.leftAnodyneExtensions_unionProd_horn₁₀_ι` : [Lur09, Proposition 2.1.2.6],
  `({0} × B) ∪ (Δ[1] × B₀) ↪ Δ[1] × B` is left anodyne.
* `SSet.leftAnodyneExtensions.whiskerLeft`, `whiskerRight`, and the instance that
  `(ihom X).map p` is a left fibration when `p` is.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Limits
  MorphismProperty

open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-! ### Stability instances for `leftAnodyneExtensions`

`leftAnodyneExtensions` is defined as `leftFibrations.llp` in `LeftFibrations.lean`
(without `deriving` clauses); the generic instances for `llp` classes are transported here. -/

instance : leftAnodyneExtensions.{u}.IsMultiplicative :=
  inferInstanceAs leftFibrations.llp.IsMultiplicative

instance : leftAnodyneExtensions.{u}.RespectsIso :=
  inferInstanceAs leftFibrations.llp.RespectsIso

instance : leftAnodyneExtensions.{u}.IsStableUnderCobaseChange :=
  inferInstanceAs leftFibrations.llp.IsStableUnderCobaseChange

instance : leftAnodyneExtensions.{u}.IsStableUnderRetracts :=
  inferInstanceAs leftFibrations.llp.IsStableUnderRetracts

instance : leftAnodyneExtensions.{u}.IsStableUnderTransfiniteComposition :=
  inferInstanceAs leftFibrations.llp.IsStableUnderTransfiniteComposition

instance : leftAnodyneExtensions.{u}.IsStableUnderCoproducts :=
  inferInstanceAs leftFibrations.llp.IsStableUnderCoproducts

lemma leftAnodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    leftAnodyneExtensions f :=
  MorphismProperty.of_isIso leftAnodyneExtensions f

lemma leftAnodyneExtensions_eq_llp_rlp :
    leftAnodyneExtensions.{u} = leftHornInclusions.rlp.llp :=
  rfl

/-! ### Left pairings -/

namespace Subcomplex

namespace Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)

/-- The condition that a pairing only involves left horns
(the `ne_last` half of `Pairing.IsInner`). -/
class IsLeft [P.IsProper] : Prop where
  ne_last (x : P.II) {d : ℕ} (hd : x.1.dim = d) :
    (P.isUniquelyCodimOneFace x).index hd ≠ Fin.last _

instance [P.IsProper] [P.IsInner] : P.IsLeft where
  ne_last := IsInner.ne_last

variable {Y : SSet.{u}} {B : Y.Subcomplex}

instance [P.IsProper] [P.IsLeft] (e : Y ≅ X) (hA : A.preimage e.hom = B) :
    (P.ofIso e hA).IsLeft where
  ne_last := by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective b
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
    simpa only [P.ofIso_index e hA ⟨a, hb⟩ hd] using IsLeft.ne_last ⟨a, hb⟩ hd

end Pairing

namespace PairingCore

variable {X : SSet.{u}} {A : X.Subcomplex} (h : A.PairingCore)

/-- The condition that `h : A.PairingCore` involves only left horns. -/
class IsLeft where
  ne_last (s : h.ι) : h.index s ≠ Fin.last _

instance [h.IsInner] : h.IsLeft where
  ne_last := IsInner.ne_last

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [h.IsLeft] [h.IsProper] : h.pairing.IsLeft where
  ne_last x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsLeft.ne_last s

end PairingCore

/-- A regular left pairing on a subcomplex `A` exhibits `A.ι` as a left anodyne
extension (the left analogue of `Pairing.innerAnodyneExtensions`). -/
lemma Pairing.leftAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] [P.IsLeft] :
    leftAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      have hn := Fin.lt_last_iff_ne_last.mpr (IsLeft.ne_last c.s rfl)
      exact .horn_ι hn⟩

end Subcomplex

/-! ### The pushout-product of a left horn inclusion with `∂Δ[n] ↪ Δ[n]` -/

namespace prodStdSimplex

instance {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    (pairingCore.{u} k n).IsLeft where
  ne_last x := by
    dsimp [pairingCore]
    simp

instance {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    (pairing.{u} k.castSucc n).IsLeft := by
  simp only [pairing_castSucc]
  infer_instance

/-- The inclusion `(Λ[m + 1, k] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ↪ Δ[m + 1] ⊗ Δ[n]`
is left anodyne for `k < Fin.last (m + 1)`. -/
lemma leftAnodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2))
    (hn : k < Fin.last (m + 1)) (n : ℕ) :
    leftAnodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι := by
  obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hn)
  exact (pairing k.castSucc n).leftAnodyneExtensions

end prodStdSimplex

/-! ### Pushout-products and pullback-homs -/

section

variable {X₁ X₂ Y₁ Y₂ E B : SSet.{u}}
  {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂} {p : E ⟶ B}

/-- [Lur09, Corollary 2.1.2.9]: if `i` is a monomorphism and `p` a left fibration, the
map from `Y₁ ⟶[SSet] E` to the pullback of `X₁ ⟶[SSet] E` and `Y₁ ⟶[SSet] B` over
`X₁ ⟶[SSet] B` is a left fibration. -/
lemma leftFibration_pullbackObjObjπ [Mono i] [LeftFibration p]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    LeftFibration sq₁₃.π := by
  rw [leftFibration_iff]
  intro _ _ _ ⟨k, hn⟩
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[_, k].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  suffices leftAnodyneExtensions sq₁₂.ι from
    this _ (by rwa [← leftFibration_iff])
  intro E B p hp
  rw [HasLiftingProperty.iff_of_arrow_iso_left
    (show Arrow.mk sq₁₂.ι ≅ Arrow.mk sq₁₂.flipTensor.ι from
      Arrow.isoMk (Iso.refl _) (β_ _ _))]
  let sq₁₃' := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom Λ[_, k].ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃']
  suffices (MorphismProperty.monomorphisms _).rlp sq₁₃'.π from this _ inferInstance
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} _ _),
    Subcomplex.unionProd.pushoutObjObj_ι]
  exact prodStdSimplex.leftAnodyneExtensions_unionProd_ι k hn n _ hp

/-- [Lur09, Corollary 2.1.2.7]: the pushout-product of a monomorphism `i` and a left
anodyne extension `j` is a left anodyne extension. -/
lemma leftAnodyneExtensions_pushoutObjObjι
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : leftAnodyneExtensions j) :
    leftAnodyneExtensions sq₁₂.ι := by
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  apply hj
  rw [← leftFibration_iff] at hp ⊢
  exact leftFibration_pullbackObjObjπ sq₁₃

/-- [Lur09, Corollary 2.1.2.7], symmetric form. -/
lemma leftAnodyneExtensions_pushoutObjObjι'
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j)
    [Mono j] (hi : leftAnodyneExtensions i) :
    leftAnodyneExtensions sq₁₂.ι := by
  refine (leftAnodyneExtensions.arrow_mk_iso_iff ?_).1
    (leftAnodyneExtensions_pushoutObjObjι sq₁₂.flipTensor hi)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

end

/-- [Lur09, Corollary 2.1.2.7] in `unionProd` form: if the inclusion of `B ⊆ Y` is left
anodyne then `(A ⊗ Y) ∪ (X ⊗ B) ↪ X ⊗ Y` is left anodyne for any subcomplex `A ⊆ X`. -/
lemma leftAnodyneExtensions_unionProd_ι
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hB : leftAnodyneExtensions B.ι) :
    leftAnodyneExtensions (A.unionProd B).ι :=
  leftAnodyneExtensions_pushoutObjObjι (Subcomplex.unionProd.pushoutObjObj A B) hB

/-- [Lur09, Corollary 2.1.2.7] in `unionProd` form, symmetric version. -/
lemma leftAnodyneExtensions_unionProd_ι'
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hA : leftAnodyneExtensions A.ι) :
    leftAnodyneExtensions (A.unionProd B).ι :=
  leftAnodyneExtensions_pushoutObjObjι' (Subcomplex.unionProd.pushoutObjObj A B) hA

/-- [Lur09, Proposition 2.1.2.6]: for any subcomplex `B₀ ⊆ B`, the inclusion
`({0} × B) ∪ (Δ[1] × B₀) ↪ Δ[1] × B` is left anodyne, where `{0} = Λ[1, 0] ⊆ Δ[1]`. -/
theorem leftAnodyneExtensions_unionProd_horn₁₀_ι {B : SSet.{u}} (B₀ : B.Subcomplex) :
    leftAnodyneExtensions ((horn 1 0).unionProd B₀).ι :=
  leftAnodyneExtensions_unionProd_ι' _ _
    (leftAnodyneExtensions.horn_ι (show (0 : Fin 2) < Fin.last 1 by decide))

/-- Left anodyne extensions are stable under `- ⊗ Z`. -/
lemma leftAnodyneExtensions.whiskerRight
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : leftAnodyneExtensions f) (Z : SSet.{u}) :
    leftAnodyneExtensions (f ▷ Z) :=
  leftAnodyneExtensions_pushoutObjObjι'
    (.ofIsInitialRight (curriedTensor _) f (initial.to Z) initialIsInitial) hf

/-- Left anodyne extensions are stable under `Z ⊗ -`. -/
lemma leftAnodyneExtensions.whiskerLeft
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : leftAnodyneExtensions f) (Z : SSet.{u}) :
    leftAnodyneExtensions (Z ◁ f) :=
  leftAnodyneExtensions_pushoutObjObjι
    (.ofIsInitialLeft (curriedTensor _) (initial.to Z) f initialIsInitial) hf

/-- For a left fibration `p : E ⟶ B` and any `X`, `(ihom X).map p : (X ⟶[SSet] E) ⟶ (X ⟶[SSet] B)`
is a left fibration. -/
instance {E B X : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    LeftFibration ((ihom X).map p) :=
  leftFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
    MonoidalClosed.internalHom (initial.to X) p initialIsInitial)

end SSet
