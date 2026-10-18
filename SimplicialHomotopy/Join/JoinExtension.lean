/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Join.JoinAnodyne

/-!
# Extending a map off the pushout-join of a boundary and an inner horn

The geometric core of Kerodon 4.3.6.8 (Tag 01BZ) and 4.3.6.1, isolated from the two ways of
transposing it (through the coslice `X_{g/}` or through the slice `X_{/b}`):

* `SSet.exists_join_extension_boundary` — for an ∞-category `X`, a morphism on
  `Δ[p] ⋆ Λ[n+1, i]` and a morphism on `∂Δ[p] ⋆ Δ[n+1]` which agree on `∂Δ[p] ⋆ Λ[n+1, i]`
  extend to a morphism on `Δ[p] ⋆ Δ[n+1]`, provided `i < Fin.last (n+1)`.

No cell induction is required: the union `(Δ[p] ⋆ Λ[n+1, i]) ∪ (∂Δ[p] ⋆ Δ[n+1])` *is* an inner
horn of `Δ[p] ⋆ Δ[n+1] ≅ Δ[p+n+2]` (`SSet.innerAnodyneExtensions_joinSub_sup`), which `X` fills
because it is a quasicategory. The two halves are glued over `∂Δ[p] ⋆ Λ[n+1, i]` using
`SSet.Subcomplex.joinSub_inf`, which makes the union a pushout square, and the identifications
`SSet.Subcomplex.joinSubRightIso`, `SSet.Subcomplex.joinSubLeftIso`.
-/

universe u

open CategoryTheory Limits Opposite Simplicial SimplexCategory

namespace SSet

/-- The geometric core of Kerodon 4.3.6.8 and 4.3.6.1: two morphisms out of `Δ[p] ⋆ Λ[n+1, i]`
and out of `∂Δ[p] ⋆ Δ[n+1]` agreeing on the intersection `∂Δ[p] ⋆ Λ[n+1, i]` extend over
`Δ[p] ⋆ Δ[n+1]`, because their common domain is an inner horn of the join. -/
lemma exists_join_extension_boundary (X : SSet.{u}) [Quasicategory X] (p : ℕ) {n : ℕ}
    (i : Fin (n + 2)) (hi : i < Fin.last (n + 1))
    (F : join (Δ[p] : SSet.{u}) (Λ[n + 1, i] : SSet.{u}) ⟶ X)
    (G : join ((boundary p : (Δ[p] : SSet.{u}).Subcomplex) : SSet.{u})
      (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hFG : joinMap (boundary p).ι (𝟙 (Λ[n + 1, i] : SSet.{u})) ≫ F =
      joinMap (𝟙 ((boundary p : (Δ[p] : SSet.{u}).Subcomplex) : SSet.{u}))
        Λ[n + 1, i].ι ≫ G) :
    ∃ H : join (Δ[p] : SSet.{u}) (Δ[n + 1] : SSet.{u}) ⟶ X,
      joinMap (𝟙 (Δ[p] : SSet.{u})) Λ[n + 1, i].ι ≫ H = F ∧
        joinMap (boundary p).ι (𝟙 (Δ[n + 1] : SSet.{u})) ≫ H = G := by
  -- the union `(Δ[p] ⋆ Λ[n+1, i]) ∪ (∂Δ[p] ⋆ Δ[n+1])` is a pushout over `∂Δ[p] ⋆ Λ[n+1, i]`
  have hinf : Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[n + 1, i] ⊓
      Subcomplex.joinSub (boundary p) (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex) =
      Subcomplex.joinSub (boundary p) Λ[n + 1, i] := by
    rw [Subcomplex.joinSub_inf, top_inf_eq, inf_top_eq]
  have bsq : Subcomplex.BicartSq
      (Subcomplex.joinSub (boundary p) Λ[n + 1, i])
      (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[n + 1, i])
      (Subcomplex.joinSub (boundary p) (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex))
      (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[n + 1, i] ⊔
        Subcomplex.joinSub (boundary p) (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex)) := ⟨rfl, hinf⟩
  -- the two inclusions of `∂Δ[p] ⋆ Λ[n+1, i]`, read inside the join
  have hα : joinMap (boundary p).ι (𝟙 (Λ[n + 1, i] : SSet.{u})) ≫
      (Subcomplex.joinSubRightIso (Δ[p] : SSet.{u}) Λ[n + 1, i]).hom =
      (Subcomplex.joinSubIso (boundary p) Λ[n + 1, i]).hom ≫ Subcomplex.homOfLE bsq.le₁₂ := by
    rw [← cancel_mono (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[n + 1, i]).ι]
    simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.joinSubRightIso_hom_ι,
      Subcomplex.joinSubIso_hom, Subcomplex.joinToSub_ι, ← joinMap_comp, Category.comp_id,
      Category.id_comp]
  have hβ : joinMap (𝟙 ((boundary p : (Δ[p] : SSet.{u}).Subcomplex) : SSet.{u}))
      Λ[n + 1, i].ι ≫
      (Subcomplex.joinSubLeftIso (boundary p) (Δ[n + 1] : SSet.{u})).hom =
      (Subcomplex.joinSubIso (boundary p) Λ[n + 1, i]).hom ≫ Subcomplex.homOfLE bsq.le₁₃ := by
    rw [← cancel_mono (Subcomplex.joinSub (boundary p) (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex)).ι]
    simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.joinSubLeftIso_hom_ι,
      Subcomplex.joinSubIso_hom, Subcomplex.joinToSub_ι, ← joinMap_comp, Category.comp_id,
      Category.id_comp]
  have h₂ : Subcomplex.homOfLE bsq.le₁₂ ≫
      (Subcomplex.joinSubRightIso (Δ[p] : SSet.{u}) Λ[n + 1, i]).inv =
      (Subcomplex.joinSubIso (boundary p) Λ[n + 1, i]).inv ≫
        joinMap (boundary p).ι (𝟙 (Λ[n + 1, i] : SSet.{u})) := by
    rw [← cancel_epi (Subcomplex.joinSubIso (boundary p) Λ[n + 1, i]).hom,
      Iso.hom_inv_id_assoc, ← Category.assoc, ← hα, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h₃ : Subcomplex.homOfLE bsq.le₁₃ ≫
      (Subcomplex.joinSubLeftIso (boundary p) (Δ[n + 1] : SSet.{u})).inv =
      (Subcomplex.joinSubIso (boundary p) Λ[n + 1, i]).inv ≫
        joinMap (𝟙 ((boundary p : (Δ[p] : SSet.{u}).Subcomplex) : SSet.{u})) Λ[n + 1, i].ι := by
    rw [← cancel_epi (Subcomplex.joinSubIso (boundary p) Λ[n + 1, i]).hom,
      Iso.hom_inv_id_assoc, ← Category.assoc, ← hβ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  -- the glued map on the union
  have w : Subcomplex.homOfLE bsq.le₁₂ ≫
      ((Subcomplex.joinSubRightIso (Δ[p] : SSet.{u}) Λ[n + 1, i]).inv ≫ F) =
      Subcomplex.homOfLE bsq.le₁₃ ≫
        ((Subcomplex.joinSubLeftIso (boundary p) (Δ[n + 1] : SSet.{u})).inv ≫ G) := by
    rw [← Category.assoc, ← Category.assoc, h₂, h₃, Category.assoc, Category.assoc, hFG]
  have hφ₂ := bsq.isPushout.inl_desc _ _ w
  have hφ₃ := bsq.isPushout.inr_desc _ _ w
  -- the union is an inner horn of `Δ[p] ⋆ Δ[n+1] ≅ Δ[p+n+2]`, so `X` fills it
  have hlift : HasLiftingProperty
      (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[n + 1, i] ⊔
        Subcomplex.joinSub (boundary p) (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex)).ι
      (terminal.from X) :=
    innerAnodyneExtensions_joinSub_sup p n i hi _ (mem_innerFibrations _)
  have sq' : CommSq (bsq.isPushout.desc _ _ w)
      (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[n + 1, i] ⊔
        Subcomplex.joinSub (boundary p) (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex)).ι
      (terminal.from X) (terminal.from _) := ⟨terminalIsTerminal.hom_ext _ _⟩
  have hℓ := sq'.fac_left
  refine ⟨sq'.lift, ?_, ?_⟩
  · calc joinMap (𝟙 (Δ[p] : SSet.{u})) Λ[n + 1, i].ι ≫ sq'.lift
        = (Subcomplex.joinSubRightIso (Δ[p] : SSet.{u}) Λ[n + 1, i]).hom ≫
            Subcomplex.homOfLE bsq.le₂₄ ≫
              (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[n + 1, i] ⊔
                Subcomplex.joinSub (boundary p)
                  (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex)).ι ≫ sq'.lift := by
          rw [Subcomplex.homOfLE_ι_assoc, ← Subcomplex.joinSubRightIso_hom_ι_assoc]
      _ = (Subcomplex.joinSubRightIso (Δ[p] : SSet.{u}) Λ[n + 1, i]).hom ≫
            ((Subcomplex.joinSubRightIso (Δ[p] : SSet.{u}) Λ[n + 1, i]).inv ≫ F) := by
          rw [hℓ, hφ₂]
      _ = F := by rw [Iso.hom_inv_id_assoc]
  · calc joinMap (boundary p).ι (𝟙 (Δ[n + 1] : SSet.{u})) ≫ sq'.lift
        = (Subcomplex.joinSubLeftIso (boundary p) (Δ[n + 1] : SSet.{u})).hom ≫
            Subcomplex.homOfLE bsq.le₃₄ ≫
              (Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) Λ[n + 1, i] ⊔
                Subcomplex.joinSub (boundary p)
                  (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex)).ι ≫ sq'.lift := by
          rw [Subcomplex.homOfLE_ι_assoc, ← Subcomplex.joinSubLeftIso_hom_ι_assoc]
      _ = (Subcomplex.joinSubLeftIso (boundary p) (Δ[n + 1] : SSet.{u})).hom ≫
            ((Subcomplex.joinSubLeftIso (boundary p) (Δ[n + 1] : SSet.{u})).inv ≫ G) := by
          rw [hℓ, hφ₃]
      _ = G := by rw [Iso.hom_inv_id_assoc]

end SSet
