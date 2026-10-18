/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Anodyne.Deformation
import SimplicialHomotopy.Anodyne.RightAnodyneCells
import SimplicialHomotopy.Anodyne.BaseChangeClosure
import SimplicialHomotopy.Equivalence.WeakEquivalenceKan
import SimplicialHomotopy.Anodyne.LeftAnodyne

/-!
# Left fibrations are smooth: base change preserves right anodyne maps

This file proves the "smoothness" half of [Lur09, Proposition 4.1.2.15]: the base change of a
right anodyne extension along a left fibration is again a right anodyne extension.  It is the
step of Joyal's Theorem A (`SSet.HTT.isCofinal_of_weaklyContractible`) that converts the
factorization `p = i ≫ q` of a map into the fibres `pullback p (C.underProj c)`.

## Mathematics

By the induction principle `SSet.rightAnodyneExtensions_le_of_nat` and the closure properties
of `SSet.baseChangeAlong leftFibrations rightAnodyneExtensions` (`BaseChangeClosure.lean`), it
suffices to treat the base change `s : Λ[n, i] ×_{Δ[n]} E ⟶ E` of a right horn inclusion
(`0 < i`) along a left fibration `π : E ⟶ Δ[n]`.  This is done by exhibiting `s` as a
deformation retract in the generalized sense of
`SSet.rightAnodyneExtensions_of_deformation`:

* `Δ[n]` retracts onto `Λ[n, i]` along the homotopy `H (j, t) = if t = 0 then j else max j i`
  (`SSet.hornDeformation`); at time `0` this is the identity, at time `1` it is `max (·, i)`,
  whose image lies in the face opposite the vertex `0 ≠ i`, hence in the horn
  (`SSet.hornRetract`).  The homotopy preserves the horn (`SSet.hornDeformationHorn`): a
  simplex misses some vertex `j ≠ i`, and `max (·, i)` cannot create the value `j`.
* Since `π` is a left fibration, `H` lifts from time `0` (where the lift is the identity of
  `E`) to a homotopy `G : E ⊗ Δ[1] ⟶ E` over `H`.  Its time-`1` end lands over `Λ[n, i]`,
  giving `q : E ⟶ Λ[n, i] ×_{Δ[n]} E` with `ι₁ ≫ G = q ≫ s`, and `G` restricts along `s` to the
  homotopy induced by `H` on the horn.

## Main statements

* `SSet.rightAnodyneExtensions_pullback_snd_horn_ι` : the horn case.
* `SSet.rightAnodyneExtensions_le_baseChangeAlong_leftFibrations` : the closure argument.
* `SSet.rightAnodyneExtensions_pullback_snd_of_leftFibration`,
  `SSet.rightAnodyneExtensions_of_isPullback_of_leftFibration` : the usable forms.
-/

universe u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace SSet

/-! ### The deformation of `Δ[n]` onto `Λ[n, i]` -/

/-- The vertex-wise formula `l ↦ if t l = 0 then x l else max (x l) i`, as a monotone map. -/
def hornRetractOrderHom {n m : ℕ} (i : Fin (n + 1)) (x : Fin (m + 1) →o Fin (n + 1))
    (t : Fin (m + 1) →o Fin 2) : Fin (m + 1) →o Fin (n + 1) where
  toFun l := if t l = 0 then x l else max (x l) i
  monotone' a b hab := by
    dsimp only
    by_cases ha : t a = 0 <;> by_cases hb : t b = 0 <;> simp only [ha, hb, ite_true, ite_false]
    · exact x.monotone hab
    · exact (x.monotone hab).trans (le_max_left _ _)
    · exact absurd (le_antisymm (hb ▸ t.monotone hab) (Fin.zero_le _)) ha
    · exact max_le_max (x.monotone hab) le_rfl

@[simp]
lemma hornRetractOrderHom_apply {n m : ℕ} (i : Fin (n + 1)) (x : Fin (m + 1) →o Fin (n + 1))
    (t : Fin (m + 1) →o Fin 2) (l : Fin (m + 1)) :
    hornRetractOrderHom i x t l = if t l = 0 then x l else max (x l) i := rfl

/-- The homotopy `Δ[n] ⊗ Δ[1] ⟶ Δ[n]`, `(j, t) ↦ if t = 0 then j else max j i`, from the
identity (time `0`) to the retraction `max (·, i)` of `Δ[n]` onto `Λ[n, i]` (time `1`). -/
noncomputable def hornDeformation (n : ℕ) (i : Fin (n + 1)) : Δ[n] ⊗ Δ[1] ⟶ Δ[n] where
  app _ := ↾fun x ↦ stdSimplex.objMk
    (hornRetractOrderHom i (stdSimplex.objEquiv x.1).toOrderHom
      (stdSimplex.objEquiv x.2).toOrderHom)
  naturality _ _ _ := rfl

variable (n : ℕ) (i : Fin (n + 1))

@[simp]
lemma hornDeformation_app_apply {d : ℕ} (x : (Δ[n] ⊗ Δ[1] : SSet.{u}).obj (op ⦋d⦌))
    (l : Fin (d + 1)) :
    (hornDeformation n i).app _ x l = if x.2 l = 0 then x.1 l else max (x.1 l) i := rfl

lemma ι₀_hornDeformation : ι₀ ≫ hornDeformation n i = 𝟙 _ := by
  ext ⟨⟨d⟩⟩ x l
  rfl

variable {n i}

/-- Time `1` of `hornDeformation` lands in the horn `Λ[n, i]` when `0 < i`. -/
lemma range_ι₁_comp_hornDeformation_le (hi : 0 < i) :
    Subcomplex.range (ι₁ ≫ hornDeformation n i) ≤ Λ[n, i] := by
  rintro ⟨⟨d⟩⟩ _ ⟨x, rfl⟩
  rw [mem_horn_iff_notMem_range]
  refine ⟨0, hi.ne, ?_⟩
  rintro ⟨l, hl⟩
  change max (x l) i = 0 at hl
  exact hi.ne' (le_antisymm ((le_max_right _ _).trans hl.le) (Fin.zero_le _))

/-- `hornDeformation` preserves the horn `Λ[n, i]`. -/
lemma range_whiskerRight_horn_ι_comp_hornDeformation_le :
    Subcomplex.range ((Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι ▷ Δ[1] ≫ hornDeformation n i) ≤
      Λ[n, i] := by
  rintro ⟨⟨d⟩⟩ _ ⟨⟨⟨x, hx⟩, t⟩, rfl⟩
  rw [mem_horn_iff_notMem_range] at hx ⊢
  obtain ⟨j, hji, hj⟩ := hx
  refine ⟨j, hji, ?_⟩
  rintro ⟨l, hl⟩
  refine hj ⟨l, ?_⟩
  change (if t l = 0 then x l else max (x l) i) = j at hl
  split_ifs at hl with h
  · exact hl
  · rcases max_choice (x l) i with h' | h'
    · rwa [h'] at hl
    · exact absurd (h' ▸ hl).symm hji

variable (n i)

/-- The retraction `max (·, i) : Δ[n] ⟶ Λ[n, i]` (`0 < i`). -/
noncomputable def hornRetract (hi : 0 < i) : Δ[n] ⟶ (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex) :=
  Subcomplex.lift _ (range_ι₁_comp_hornDeformation_le hi)

@[reassoc (attr := simp)]
lemma hornRetract_ι (hi : 0 < i) :
    hornRetract n i hi ≫ Λ[n, i].ι = ι₁ ≫ hornDeformation n i := rfl

/-- The restriction of `hornDeformation` to the horn. -/
noncomputable def hornDeformationHorn :
    ((Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex) : SSet.{u}) ⊗ Δ[1] ⟶
      (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex) :=
  Subcomplex.lift _ range_whiskerRight_horn_ι_comp_hornDeformation_le

@[reassoc (attr := simp)]
lemma hornDeformationHorn_ι :
    hornDeformationHorn n i ≫ Λ[n, i].ι = Λ[n, i].ι ▷ Δ[1] ≫ hornDeformation n i := rfl

/-! ### Lifting the deformation along a left fibration -/

/-- `{0} ⊆ Δ[1]` is left anodyne (mirror of `rightAnodyneExtensions_face_one_ι`). -/
lemma leftAnodyneExtensions_face_zero_ι :
    leftAnodyneExtensions (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  rw [← horn_one_zero_eq_face]
  exact leftAnodyneExtensions.horn_ι (by decide)

/-- `E ⊗ {0} ⟶ E` is a split epimorphism (it is an isomorphism). -/
instance isSplitEpi_fst_face_zero (E : SSet.{u}) :
    IsSplitEpi (fst E (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)) :=
  IsSplitEpi.mk' ⟨lift (𝟙 E)
    (stdSimplex.isTerminalObj₀.from E ≫ (stdSimplex.faceSingletonIso (0 : Fin 2)).hom),
    lift_fst _ _⟩

/-- [Lur09, 4.1.2.15], horn case: the base change of a right horn inclusion `Λ[n, i] ⊆ Δ[n]`
(`0 < i`) along a left fibration `π : E ⟶ Δ[n]` is right anodyne. -/
theorem rightAnodyneExtensions_pullback_snd_horn_ι {n : ℕ} {i : Fin (n + 1)} (hi : 0 < i)
    {E : SSet.{u}} (π : E ⟶ Δ[n]) [LeftFibration π] :
    rightAnodyneExtensions (pullback.snd (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι π) := by
  have hlift : HasLiftingProperty
      (E ◁ (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) π :=
    (leftAnodyneExtensions_face_zero_ι.whiskerLeft E) _ (mem_leftFibrations π)
  have sq : CommSq (fst E _) (E ◁ (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι) π
      (π ▷ Δ[1] ≫ hornDeformation n i) :=
    ⟨by rw [whiskerLeft_face_zero_ι, Category.assoc, ι₀_comp_assoc, ι₀_hornDeformation,
      Category.comp_id]⟩
  have hG₀ : ι₀ ≫ sq.lift = 𝟙 E := by
    rw [← cancel_epi (fst E (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)),
      ← Category.assoc, ← whiskerLeft_face_zero_ι, sq.fac_left, Category.comp_id]
  have hq : (π ≫ hornRetract n i hi) ≫ Λ[n, i].ι = (ι₁ ≫ sq.lift) ≫ π := by
    rw [Category.assoc, hornRetract_ι, Category.assoc, sq.fac_right, ι₁_comp_assoc]
  have hG' : (pullback.fst Λ[n, i].ι π ▷ Δ[1] ≫ hornDeformationHorn n i) ≫ Λ[n, i].ι =
      (pullback.snd Λ[n, i].ι π ▷ Δ[1] ≫ sq.lift) ≫ π := by
    rw [Category.assoc, hornDeformationHorn_ι, Category.assoc, sq.fac_right, ← Category.assoc,
      ← comp_whiskerRight, ← Category.assoc, ← comp_whiskerRight, pullback.condition]
  exact rightAnodyneExtensions_of_deformation (pullback.snd Λ[n, i].ι π)
    (pullback.lift (π ≫ hornRetract n i hi) (ι₁ ≫ sq.lift) hq) sq.lift
    (pullback.lift _ _ hG') hG₀ (pullback.lift_snd _ _ _).symm (pullback.lift_snd _ _ _).symm

/-! ### The closure argument -/

/-- Right horn inclusions pull back along left fibrations to right anodyne extensions. -/
theorem rightHornInclusions_le_baseChangeAlong_leftFibrations :
    rightHornInclusions.{u} ≤ baseChangeAlong leftFibrations rightAnodyneExtensions := by
  rintro _ _ _ ⟨i, hi⟩ E π hπ
  have : LeftFibration π := ⟨hπ⟩
  exact rightAnodyneExtensions_pullback_snd_horn_ι hi π

/-- [Lur09, Proposition 4.1.2.15] (left fibrations are smooth): every base change of a right
anodyne extension along a left fibration is a right anodyne extension. -/
theorem rightAnodyneExtensions_le_baseChangeAlong_leftFibrations :
    rightAnodyneExtensions.{u} ≤ baseChangeAlong leftFibrations rightAnodyneExtensions :=
  rightAnodyneExtensions_le_of_nat rightHornInclusions_le_baseChangeAlong_leftFibrations

/-- [Lur09, Proposition 4.1.2.15] for the chosen pullback: the base change `pullback.snd f p`
of a right anodyne extension `f` along a left fibration `p` is right anodyne. -/
theorem rightAnodyneExtensions_pullback_snd_of_leftFibration {A B E : SSet.{u}} {f : A ⟶ B}
    (hf : rightAnodyneExtensions f) (p : E ⟶ B) [LeftFibration p] :
    rightAnodyneExtensions (pullback.snd f p) :=
  rightAnodyneExtensions_le_baseChangeAlong_leftFibrations _ hf p (mem_leftFibrations p)

/-- [Lur09, Proposition 4.1.2.15] for an arbitrary pullback square: if `f` is right anodyne,
`p` is a left fibration and `IsPullback a g f p`, then `g` is right anodyne. -/
theorem rightAnodyneExtensions_of_isPullback_of_leftFibration {A B X E : SSet.{u}} {f : A ⟶ B}
    (hf : rightAnodyneExtensions f) {p : E ⟶ B} [LeftFibration p] {a : X ⟶ A} {g : X ⟶ E}
    (sq : IsPullback a g f p) : rightAnodyneExtensions g :=
  (rightAnodyneExtensions_le_baseChangeAlong_leftFibrations _ hf).of_isPullback
    (mem_leftFibrations p) sq

end SSet
