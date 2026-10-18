/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.RightFibrations
import SimplicialHomotopy.Anodyne.LeftAnodyne
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Op

/-!
# Right anodyne extensions and pushout-products, right fibrations and pullbacks

The mirror image of `SimplicialHomotopy.Anodyne.LeftAnodyne` for *right* anodyne extensions and
*right* fibrations (`SimplicialHomotopy.Fibration.RightFibrations`).

* `SSet.Subcomplex.Pairing.IsRight`, `SSet.Subcomplex.PairingCore.IsRight` : a pairing only
  involves *right* horns (`index ≠ 0`); an inner pairing is a right pairing, the opposite of a
  left pairing is a right pairing (`SSet.Subcomplex.IsUniquelyCodimOneFace.op_index`).
* `SSet.Subcomplex.Pairing.rightAnodyneExtensions` : a regular right pairing on `A` exhibits
  `A.ι` as a right anodyne extension.
* `SSet.prodStdSimplex.rightAnodyneExtensions_unionProd_ι` :
  `(Λ[m + 1, k] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ↪ Δ[m + 1] ⊗ Δ[n]` is right anodyne for `0 < k`.
* `SSet.rightFibration_pullbackObjObjπ` : the pullback-hom of a monomorphism and a right
  fibration is a right fibration ([Lur09, Corollary 2.1.2.9], dual form).
* `SSet.rightAnodyneExtensions_pushoutObjObjι`, `…ι'`, `SSet.rightAnodyneExtensions_unionProd_ι`,
  `…ι'` : the pushout-product of a monomorphism and a right anodyne extension is right anodyne
  ([Lur09, Corollary 2.1.2.7], dual form).
* `SSet.rightAnodyneExtensions_unionProd_horn₁₁_ι` : [Lur09, Proposition 2.1.2.6], dual form:
  `({1} × B) ∪ (Δ[1] × B₀) ↪ Δ[1] × B` is right anodyne.
* `SSet.rightAnodyneExtensions.whiskerLeft`, `whiskerRight`, and the instance that
  `(ihom X).map p` is a right fibration when `p` is.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Limits
  MorphismProperty

open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

/-! ### Stability instances for `rightAnodyneExtensions` -/

instance : rightAnodyneExtensions.{u}.IsMultiplicative :=
  inferInstanceAs rightFibrations.llp.IsMultiplicative

instance : rightAnodyneExtensions.{u}.RespectsIso :=
  inferInstanceAs rightFibrations.llp.RespectsIso

instance : rightAnodyneExtensions.{u}.IsStableUnderCobaseChange :=
  inferInstanceAs rightFibrations.llp.IsStableUnderCobaseChange

instance : rightAnodyneExtensions.{u}.IsStableUnderRetracts :=
  inferInstanceAs rightFibrations.llp.IsStableUnderRetracts

instance : rightAnodyneExtensions.{u}.IsStableUnderTransfiniteComposition :=
  inferInstanceAs rightFibrations.llp.IsStableUnderTransfiniteComposition

instance : rightAnodyneExtensions.{u}.IsStableUnderCoproducts :=
  inferInstanceAs rightFibrations.llp.IsStableUnderCoproducts

lemma rightAnodyneExtensions.of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    rightAnodyneExtensions f :=
  MorphismProperty.of_isIso rightAnodyneExtensions f

lemma rightAnodyneExtensions_eq_llp_rlp :
    rightAnodyneExtensions.{u} = rightHornInclusions.rlp.llp :=
  rfl

/-! ### Right pairings -/

namespace Subcomplex

/-- The index of the opposite of a uniquely codimension one face is the reversed index. -/
lemma IsUniquelyCodimOneFace.op_index {X : SSet.{u}} {x y : X.S}
    (hxy : x.IsUniquelyCodimOneFace y) {d : ℕ} (hd : x.dim = d)
    (hd' : (S.opEquiv.symm x).dim = d) :
    hxy.op.index hd' = (hxy.index hd).rev := by
  refine ((hxy.op.δ_eq_iff hd' _).1 ?_).symm
  obtain ⟨d₀, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d₀ + 1 := hxy.dim_eq
  obtain rfl : d₀ = d := hd
  have h := hxy.δ_index rfl
  simp only [S.cast_simplex_rfl] at h
  change X.op.δ _ (opObjEquiv.symm y) = opObjEquiv.symm x
  simpa using h

namespace Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)

/-- The condition that a pairing only involves right horns
(the `ne_zero` half of `Pairing.IsInner`). -/
class IsRight [P.IsProper] : Prop where
  ne_zero (x : P.II) {d : ℕ} (hd : x.1.dim = d) :
    (P.isUniquelyCodimOneFace x).index hd ≠ 0

instance [P.IsProper] [P.IsInner] : P.IsRight where
  ne_zero := IsInner.ne_zero

variable {Y : SSet.{u}} {B : Y.Subcomplex}

instance [P.IsProper] [P.IsRight] (e : Y ≅ X) (hA : A.preimage e.hom = B) :
    (P.ofIso e hA).IsRight where
  ne_zero := by
    rintro ⟨b, hb⟩ d hd
    obtain ⟨a, rfl⟩ := (N.orderIsoOfIso e hA).symm.surjective b
    simp only [ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at hb
    simpa only [P.ofIso_index e hA ⟨a, hb⟩ hd] using IsRight.ne_zero ⟨a, hb⟩ hd

/-- The opposite of a left pairing is a right pairing. -/
instance [P.IsProper] [P.IsLeft] : P.op.IsRight where
  ne_zero x d hd := by
    have hd₀ : (⟨N.opEquiv x.1, x.2⟩ : P.II).1.toS.dim = d := hd
    have key := IsUniquelyCodimOneFace.op_index
      (P.isUniquelyCodimOneFace ⟨N.opEquiv x.1, x.2⟩) hd₀ hd
    intro h
    have h' : ((P.isUniquelyCodimOneFace ⟨N.opEquiv x.1, x.2⟩).index hd₀).rev = 0 :=
      key.symm.trans h
    exact IsLeft.ne_last ⟨N.opEquiv x.1, x.2⟩ hd₀ (by simpa [Fin.rev_eq_iff] using h')

/-- The opposite of a right pairing is a left pairing. -/
instance [P.IsProper] [P.IsRight] : P.op.IsLeft where
  ne_last x d hd := by
    have hd₀ : (⟨N.opEquiv x.1, x.2⟩ : P.II).1.toS.dim = d := hd
    have key := IsUniquelyCodimOneFace.op_index
      (P.isUniquelyCodimOneFace ⟨N.opEquiv x.1, x.2⟩) hd₀ hd
    intro h
    have h' : ((P.isUniquelyCodimOneFace ⟨N.opEquiv x.1, x.2⟩).index hd₀).rev = Fin.last _ :=
      key.symm.trans h
    exact IsRight.ne_zero ⟨N.opEquiv x.1, x.2⟩ hd₀ (by simpa [Fin.rev_eq_iff] using h')

end Pairing

namespace PairingCore

variable {X : SSet.{u}} {A : X.Subcomplex} (h : A.PairingCore)

/-- The condition that `h : A.PairingCore` involves only right horns. -/
class IsRight where
  ne_zero (s : h.ι) : h.index s ≠ 0

instance [h.IsInner] : h.IsRight where
  ne_zero := IsInner.ne_zero

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [h.IsRight] [h.IsProper] : h.pairing.IsRight where
  ne_zero x := by
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    rintro _ rfl
    simpa using IsRight.ne_zero s

end PairingCore

/-- A regular right pairing on a subcomplex `A` exhibits `A.ι` as a right anodyne
extension (the right analogue of `Pairing.innerAnodyneExtensions`). -/
lemma Pairing.rightAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] [P.IsRight] :
    rightAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _ ) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      have hn := Fin.pos_of_ne_zero (IsRight.ne_zero c.s rfl)
      exact .horn_ι hn⟩

end Subcomplex

/-! ### The pushout-product of a right horn inclusion with `∂Δ[n] ↪ Δ[n]` -/

namespace prodStdSimplex

instance {m : ℕ} (k : Fin m) (n : ℕ) :
    (pairing.{u} k.succ.castSucc n).IsRight := by
  simp only [pairing_castSucc]
  infer_instance

/-- The inclusion `(Λ[m + 1, k] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ↪ Δ[m + 1] ⊗ Δ[n]`
is right anodyne for `0 < k`. -/
lemma rightAnodyneExtensions_unionProd_ι {m : ℕ} (k : Fin (m + 2))
    (hk : 0 < k) (n : ℕ) :
    rightAnodyneExtensions (Subcomplex.unionProd.{u} Λ[m + 1, k] ∂Δ[n]).ι := by
  by_cases hlast : k = Fin.last (m + 1)
  · subst hlast
    -- the pairing used by Mathlib for `pairing (Fin.last (m + 1)) n`, unfolded so that the
    -- `IsRight` instances for `op` and `ofIso` apply
    exact Subcomplex.Pairing.rightAnodyneExtensions
      ((pairingCore.{u} (0 : Fin (m + 1)) n).pairing.op.ofIso
        (((stdSimplex.opIso _).symm ⊗ᵢ (stdSimplex.opIso _).symm) ≪≫
          Functor.Monoidal.μIso opFunctor _ _) (by
            dsimp
            rw [Subcomplex.preimage_comp, Subcomplex.preimage_op_unionProd,
              Subcomplex.preimage_unionProd, op_boundary, op_horn, Fin.rev_zero]))
  · obtain ⟨k, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
    obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero (i := k) (by rintro rfl; simp at hk)
    exact (pairing l.succ.castSucc n).rightAnodyneExtensions

end prodStdSimplex

/-! ### Pushout-products and pullback-homs -/

section

variable {X₁ X₂ Y₁ Y₂ E B : SSet.{u}}
  {i : X₁ ⟶ Y₁} {j : X₂ ⟶ Y₂} {p : E ⟶ B}

/-- [Lur09, Corollary 2.1.2.9], dual form: if `i` is a monomorphism and `p` a right
fibration, the map from `Y₁ ⟶[SSet] E` to the pullback of `X₁ ⟶[SSet] E` and `Y₁ ⟶[SSet] B`
over `X₁ ⟶[SSet] B` is a right fibration. -/
lemma rightFibration_pullbackObjObjπ [Mono i] [RightFibration p]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    RightFibration sq₁₃.π := by
  rw [rightFibration_iff]
  intro _ _ _ ⟨k, hk⟩
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i Λ[_, k].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂]
  suffices rightAnodyneExtensions sq₁₂.ι from
    this _ (by rwa [← rightFibration_iff])
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
  exact prodStdSimplex.rightAnodyneExtensions_unionProd_ι k hk n _ hp

/-- [Lur09, Corollary 2.1.2.7], dual form: the pushout-product of a monomorphism `i` and a
right anodyne extension `j` is a right anodyne extension. -/
lemma rightAnodyneExtensions_pushoutObjObjι
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j) [Mono i] (hj : rightAnodyneExtensions j) :
    rightAnodyneExtensions sq₁₂.ι := by
  intro E B p hp
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff _ sq₁₃]
  apply hj
  rw [← rightFibration_iff] at hp ⊢
  exact rightFibration_pullbackObjObjπ sq₁₃

/-- [Lur09, Corollary 2.1.2.7], dual form, symmetric version. -/
lemma rightAnodyneExtensions_pushoutObjObjι'
    (sq₁₂ : (curriedTensor _).PushoutObjObj i j)
    [Mono j] (hi : rightAnodyneExtensions i) :
    rightAnodyneExtensions sq₁₂.ι := by
  refine (rightAnodyneExtensions.arrow_mk_iso_iff ?_).1
    (rightAnodyneExtensions_pushoutObjObjι sq₁₂.flipTensor hi)
  exact Arrow.isoMk (Iso.refl _) (β_ _ _)

end

/-- [Lur09, Corollary 2.1.2.7] in `unionProd` form: if the inclusion of `B ⊆ Y` is right
anodyne then `(A ⊗ Y) ∪ (X ⊗ B) ↪ X ⊗ Y` is right anodyne for any subcomplex `A ⊆ X`. -/
lemma rightAnodyneExtensions_unionProd_ι
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hB : rightAnodyneExtensions B.ι) :
    rightAnodyneExtensions (A.unionProd B).ι :=
  rightAnodyneExtensions_pushoutObjObjι (Subcomplex.unionProd.pushoutObjObj A B) hB

/-- [Lur09, Corollary 2.1.2.7] in `unionProd` form, symmetric version. -/
lemma rightAnodyneExtensions_unionProd_ι'
    {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
    (hA : rightAnodyneExtensions A.ι) :
    rightAnodyneExtensions (A.unionProd B).ι :=
  rightAnodyneExtensions_pushoutObjObjι' (Subcomplex.unionProd.pushoutObjObj A B) hA

/-- [Lur09, Proposition 2.1.2.6], dual form: for any subcomplex `B₀ ⊆ B`, the inclusion
`({1} × B) ∪ (Δ[1] × B₀) ↪ Δ[1] × B` is right anodyne, where `{1} = Λ[1, 1] ⊆ Δ[1]`. -/
theorem rightAnodyneExtensions_unionProd_horn₁₁_ι {B : SSet.{u}} (B₀ : B.Subcomplex) :
    rightAnodyneExtensions ((horn 1 1).unionProd B₀).ι :=
  rightAnodyneExtensions_unionProd_ι' _ _
    (rightAnodyneExtensions.horn_ι (show (0 : Fin 2) < 1 by decide))

/-- Right anodyne extensions are stable under `- ⊗ Z`. -/
lemma rightAnodyneExtensions.whiskerRight
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : rightAnodyneExtensions f) (Z : SSet.{u}) :
    rightAnodyneExtensions (f ▷ Z) :=
  rightAnodyneExtensions_pushoutObjObjι'
    (.ofIsInitialRight (curriedTensor _) f (initial.to Z) initialIsInitial) hf

/-- Right anodyne extensions are stable under `Z ⊗ -`. -/
lemma rightAnodyneExtensions.whiskerLeft
    {X Y : SSet.{u}} {f : X ⟶ Y} (hf : rightAnodyneExtensions f) (Z : SSet.{u}) :
    rightAnodyneExtensions (Z ◁ f) :=
  rightAnodyneExtensions_pushoutObjObjι
    (.ofIsInitialLeft (curriedTensor _) (initial.to Z) f initialIsInitial) hf

/-- For a right fibration `p : E ⟶ B` and any `X`,
`(ihom X).map p : (X ⟶[SSet] E) ⟶ (X ⟶[SSet] B)` is a right fibration. -/
instance {E B X : SSet.{u}} (p : E ⟶ B) [RightFibration p] :
    RightFibration ((ihom X).map p) :=
  rightFibration_pullbackObjObjπ (Functor.PullbackObjObj.ofIsInitial
    MonoidalClosed.internalHom (initial.to X) p initialIsInitial)

end SSet
