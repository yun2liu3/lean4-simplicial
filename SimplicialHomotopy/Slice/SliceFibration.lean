/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Slice.SliceDiagram
import SimplicialHomotopy.Join.JoinExtension

/-!
# Kerodon 4.3.6.8 and 4.3.6.1 for an arbitrary diagram

`Join/JoinExtension.lean` extends a morphism off
`(Δ[p] ⋆ Λ[n+1, i]) ∪ (∂Δ[p] ⋆ Δ[n+1])`. Transposing that through the *slice* `X_{/b}` of
`Slice/SliceDiagram.lean` — the adjoint of the join in its **front** variable — says that
the restriction `X_{/b} ⟶ X_{/b₀}` along a horn `Λ[n+1, i] ↪ Δ[n+1]` has the right lifting
property against every boundary inclusion `∂Δ[p] ↪ Δ[p]`. By `SSet.rlp_monomorphisms` it then
has the right lifting property against **every monomorphism**, with no cell induction: Mathlib's
`relativeCellComplexOfMono` does the induction once and for all.

Transposing back through the coslice gives the two statements the proof of Kerodon Proposition
4.4.2.13 (Tag 01H0) needs:

* `SSet.leftFibration_cosliceDiagRestrict` — **Kerodon 4.3.6.8 (Tag 01BZ)**: for a monomorphism
  `u : L₀ ⟶ L` and a diagram `g : L ⟶ X` in an ∞-category, `X_{g/} ⟶ X_{(u ≫ g)/}` is a left
  fibration.
* `SSet.leftFibration_cosliceDiagProj` — **Kerodon 4.3.6.1**: `X_{g/} ⟶ X` is a left fibration.

The second is the case `L₀ = ∅` of the first, obtained by lifting against the monomorphism
`(⊥ : L.Subcomplex).ι`.
-/

universe u

open CategoryTheory Limits Opposite Simplicial SimplexCategory

namespace SSet

variable {B K L X : SSet.{u}}

/-! ### The slice restriction lifts against monomorphisms -/

/-- The generating case: `X_{/b} ⟶ X_{/b₀}` lifts against a boundary inclusion. -/
lemma hasLiftingProperty_boundary_sliceDiagRestrict (X : SSet.{u}) [Quasicategory X] (p : ℕ)
    {n : ℕ} (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) (b : (Δ[n + 1] : SSet.{u}) ⟶ X) :
    HasLiftingProperty (boundary p).ι (sliceDiagRestrict Λ[n + 1, i].ι b) := by
  constructor
  intro a c sq
  have hcompat : joinMap (boundary p).ι (𝟙 (Λ[n + 1, i] : SSet.{u})) ≫ sliceDiagToJoin c =
      joinMap (𝟙 ((boundary p : (Δ[p] : SSet.{u}).Subcomplex) : SSet.{u})) Λ[n + 1, i].ι ≫
        sliceDiagToJoin a := by
    rw [← sliceDiagToJoin_naturality, ← sliceDiagToJoin_restrict, sq.w]
  obtain ⟨H, hH₁, hH₂⟩ := exists_join_extension_boundary X p i hi _ _ hcompat
  have hb : joinInr (Δ[p] : SSet.{u}) (Δ[n + 1] : SSet.{u}) ≫ H = b := by
    rw [← Category.id_comp (joinInr (Δ[p] : SSet.{u}) (Δ[n + 1] : SSet.{u})),
      joinInr_naturality (boundary p).ι (𝟙 (Δ[n + 1] : SSet.{u})), Category.assoc, hH₂,
      joinInr_comp_sliceDiagToJoin]
  refine ⟨⟨⟨sliceDiagFromJoin H hb, ?_, ?_⟩⟩⟩
  · apply (sliceDiagHomEquiv _ b).injective
    refine Subtype.ext ?_
    change sliceDiagToJoin ((boundary p).ι ≫ sliceDiagFromJoin H hb) = sliceDiagToJoin a
    rw [sliceDiagToJoin_naturality, sliceDiagToJoin_sliceDiagFromJoin, hH₂]
  · apply (sliceDiagHomEquiv _ (Λ[n + 1, i].ι ≫ b)).injective
    refine Subtype.ext ?_
    change sliceDiagToJoin (sliceDiagFromJoin H hb ≫ sliceDiagRestrict Λ[n + 1, i].ι b) =
      sliceDiagToJoin c
    rw [sliceDiagToJoin_restrict, sliceDiagToJoin_sliceDiagFromJoin, hH₁]

/-- `X_{/b} ⟶ X_{/b₀}` lifts against *every* monomorphism: the generating case plus
`SSet.rlp_monomorphisms`. -/
theorem hasLiftingProperty_mono_sliceDiagRestrict (X : SSet.{u}) [Quasicategory X]
    {A₀ A : SSet.{u}} (v : A₀ ⟶ A) [Mono v] {n : ℕ} (i : Fin (n + 2))
    (hi : i < Fin.last (n + 1)) (b : (Δ[n + 1] : SSet.{u}) ⟶ X) :
    HasLiftingProperty v (sliceDiagRestrict Λ[n + 1, i].ι b) := by
  have h : (MorphismProperty.monomorphisms SSet.{u}).rlp
      (sliceDiagRestrict Λ[n + 1, i].ι b) := by
    rw [rlp_monomorphisms]
    rintro _ _ _ ⟨q⟩
    exact hasLiftingProperty_boundary_sliceDiagRestrict _ q i hi b
  exact h v (MorphismProperty.monomorphisms.infer_property v)

/-! ### Kerodon 4.3.6.8 -/

/-- The transposed lifting problem of **Kerodon 4.3.6.8 (Tag 01BZ)**. -/
lemma hasLiftingProperty_horn_cosliceDiagRestrict (X : SSet.{u}) [Quasicategory X]
    {L₀ : SSet.{u}} (u : L₀ ⟶ L) [Mono u] (g : L ⟶ X) {n : ℕ} (i : Fin (n + 2))
    (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty Λ[n + 1, i].ι (cosliceDiagRestrict u g) := by
  constructor
  intro a c sq
  set F := cosliceDiagToJoin a with hFdef
  set G := cosliceDiagToJoin c with hGdef
  have hcompat : joinMap u (𝟙 (Λ[n + 1, i] : SSet.{u})) ≫ F =
      joinMap (𝟙 L₀) Λ[n + 1, i].ι ≫ G := by
    rw [hFdef, hGdef, ← cosliceDiagToJoin_restrict, ← cosliceDiagToJoin_naturality, sq.w]
  set b : (Δ[n + 1] : SSet.{u}) ⟶ X := joinInr L₀ (Δ[n + 1] : SSet.{u}) ≫ G with hbdef
  have hF : joinInr L (Λ[n + 1, i] : SSet.{u}) ≫ F = Λ[n + 1, i].ι ≫ b := by
    rw [hbdef, ← Category.assoc, joinInr_naturality (𝟙 L₀) Λ[n + 1, i].ι, Category.assoc,
      ← hcompat, ← Category.assoc, ← joinInr_naturality u (𝟙 (Λ[n + 1, i] : SSet.{u})),
      Category.id_comp]
  have hsq : CommSq (sliceDiagFromJoin G hbdef.symm) u (sliceDiagRestrict Λ[n + 1, i].ι b)
      (sliceDiagFromJoin F hF) := ⟨by
    rw [sliceDiagFromJoin_restrict, sliceDiagFromJoin_naturality]
    exact sliceDiagFromJoin_congr hcompat.symm _ _⟩
  have := hasLiftingProperty_mono_sliceDiagRestrict X u i hi b
  have hH₁ : joinMap (𝟙 L) Λ[n + 1, i].ι ≫ sliceDiagToJoin hsq.lift = F := by
    rw [← sliceDiagToJoin_restrict, hsq.fac_right, sliceDiagToJoin_sliceDiagFromJoin]
  have hH₂ : joinMap u (𝟙 (Δ[n + 1] : SSet.{u})) ≫ sliceDiagToJoin hsq.lift = G := by
    rw [← sliceDiagToJoin_naturality, hsq.fac_left, sliceDiagToJoin_sliceDiagFromJoin]
  have h₁ : joinInl L (Δ[n + 1] : SSet.{u}) ≫ sliceDiagToJoin hsq.lift = g := by
    rw [← Category.id_comp (joinInl L (Δ[n + 1] : SSet.{u})),
      joinInl_naturality (𝟙 L) Λ[n + 1, i].ι, Category.assoc, hH₁, hFdef,
      joinInl_comp_cosliceDiagToJoin]
  refine ⟨⟨⟨cosliceDiagFromJoin (sliceDiagToJoin hsq.lift) h₁, ?_, ?_⟩⟩⟩
  · apply (cosliceDiagHomEquiv _ g).injective
    refine Subtype.ext ?_
    change cosliceDiagToJoin
        (Λ[n + 1, i].ι ≫ cosliceDiagFromJoin (sliceDiagToJoin hsq.lift) h₁) = F
    rw [cosliceDiagToJoin_naturality, cosliceDiagToJoin_cosliceDiagFromJoin, hH₁]
  · apply (cosliceDiagHomEquiv _ (u ≫ g)).injective
    refine Subtype.ext ?_
    change cosliceDiagToJoin
        (cosliceDiagFromJoin (sliceDiagToJoin hsq.lift) h₁ ≫ cosliceDiagRestrict u g) = G
    rw [cosliceDiagToJoin_restrict, cosliceDiagToJoin_cosliceDiagFromJoin, hH₂]

/-- **Kerodon 4.3.6.8 (Tag 01BZ)**: for an ∞-category `X`, a diagram `g : L ⟶ X` and a
monomorphism `u : L₀ ⟶ L`, the restriction `X_{g/} ⟶ X_{(u ≫ g)/}` is a left fibration. -/
theorem leftFibration_cosliceDiagRestrict (X : SSet.{u}) [Quasicategory X] {L₀ : SSet.{u}}
    (u : L₀ ⟶ L) [Mono u] (g : L ⟶ X) : LeftFibration (cosliceDiagRestrict u g) := by
  constructor
  rintro _ _ _ ⟨i, hi⟩
  exact hasLiftingProperty_horn_cosliceDiagRestrict _ u g i hi

/-! ### Kerodon 4.3.6.1 -/

/-- The transposed lifting problem of **Kerodon 4.3.6.1**. -/
lemma hasLiftingProperty_horn_cosliceDiagProj (X : SSet.{u}) [Quasicategory X] (g : L ⟶ X)
    {n : ℕ} (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty Λ[n + 1, i].ι (cosliceDiagProj g) := by
  constructor
  intro a c sq
  set F := cosliceDiagToJoin a with hFdef
  have hF : joinInr L (Λ[n + 1, i] : SSet.{u}) ≫ F = Λ[n + 1, i].ι ≫ c := by
    rw [hFdef, ← comp_cosliceDiagProj, sq.w]
  have hsq : CommSq (default : ((⊥ : L.Subcomplex) : SSet.{u}) ⟶ sliceDiag c)
      (⊥ : L.Subcomplex).ι (sliceDiagRestrict Λ[n + 1, i].ι c) (sliceDiagFromJoin F hF) :=
    ⟨Subsingleton.elim _ _⟩
  have := hasLiftingProperty_mono_sliceDiagRestrict X (⊥ : L.Subcomplex).ι i hi c
  have hH₁ : joinMap (𝟙 L) Λ[n + 1, i].ι ≫ sliceDiagToJoin hsq.lift = F := by
    rw [← sliceDiagToJoin_restrict, hsq.fac_right, sliceDiagToJoin_sliceDiagFromJoin]
  have hH₂ : joinInr L (Δ[n + 1] : SSet.{u}) ≫ sliceDiagToJoin hsq.lift = c :=
    joinInr_comp_sliceDiagToJoin hsq.lift
  have h₁ : joinInl L (Δ[n + 1] : SSet.{u}) ≫ sliceDiagToJoin hsq.lift = g := by
    rw [← Category.id_comp (joinInl L (Δ[n + 1] : SSet.{u})),
      joinInl_naturality (𝟙 L) Λ[n + 1, i].ι, Category.assoc, hH₁, hFdef,
      joinInl_comp_cosliceDiagToJoin]
  refine ⟨⟨⟨cosliceDiagFromJoin (sliceDiagToJoin hsq.lift) h₁, ?_, ?_⟩⟩⟩
  · apply (cosliceDiagHomEquiv _ g).injective
    refine Subtype.ext ?_
    change cosliceDiagToJoin
        (Λ[n + 1, i].ι ≫ cosliceDiagFromJoin (sliceDiagToJoin hsq.lift) h₁) = F
    rw [cosliceDiagToJoin_naturality, cosliceDiagToJoin_cosliceDiagFromJoin, hH₁]
  · rw [comp_cosliceDiagProj, cosliceDiagToJoin_cosliceDiagFromJoin]
    exact hH₂

/-- **Kerodon 4.3.6.1**: for an ∞-category `X` and any diagram `g : L ⟶ X`, the projection
`X_{g/} ⟶ X` is a left fibration. -/
theorem leftFibration_cosliceDiagProj (X : SSet.{u}) [Quasicategory X] (g : L ⟶ X) :
    LeftFibration (cosliceDiagProj g) := by
  constructor
  rintro _ _ _ ⟨i, hi⟩
  exact hasLiftingProperty_horn_cosliceDiagProj _ g i hi

end SSet
