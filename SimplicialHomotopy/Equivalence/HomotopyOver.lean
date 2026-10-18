/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Equivalence.WeakEquivalence

/-!
# Homotopies over a trivial fibration

* `SSet.exists_homotopy_over_of_rlp_monomorphisms` : if `f : X ⟶ Y` is a trivial fibration and
  `a b : W ⟶ X` satisfy `a ≫ f = b ≫ f`, there is a homotopy `H : a ≃ b` with
  `H.h ≫ f = fst ≫ a ≫ f`, i.e. lying over the common composite.

This is the relative form of the argument of `SSet.isHomotopyEquivalence_of_rlp_monomorphisms`
(`Equivalence/WeakEquivalence.lean`): lift `W ⊗ ∂Δ[1] ↪ W ⊗ Δ[1]` against `f`. It is what makes
a homotopy *vertical* over a base through which `f` factors.
-/

universe u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory

open scoped Simplicial

namespace SSet

/-- Two maps into the source of a trivial fibration that agree after it are homotopic, by a
homotopy lying over the common composite. -/
theorem exists_homotopy_over_of_rlp_monomorphisms {W X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f) (a b : W ⟶ X) (hab : a ≫ f = b ≫ f) :
    ∃ H : Homotopy a b, H.h ≫ f = fst W Δ[1] ≫ a ≫ f := by
  let S : (W ⊗ Δ[1]).Subcomplex := Subcomplex.range ι₀ ⊔ Subcomplex.range ι₁
  have sq : Subcomplex.BicartSq ⊥ (Subcomplex.range ι₀) (Subcomplex.range ι₁) S :=
    { sup_eq := rfl
      inf_eq := by
        refine le_antisymm ?_ bot_le
        intro n x hx
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = Opposite.op ⦋m⦌ := ⟨n.unop.len, rfl⟩
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
        have := congr_arg (fun y : (W ⊗ Δ[1]) _⦋m⦌ ↦ (y.2 : Δ[1] _⦋m⦌) 0) (ha.trans hb.symm)
        simp at this }
  obtain ⟨top, htop₀, htop₁⟩ : ∃ top : (S : SSet) ⟶ X,
      Subcomplex.homOfLE sq.le₂₄ ≫ top = (Subcomplex.range ι₀).ι ≫ fst _ _ ≫ a ∧
      Subcomplex.homOfLE sq.le₃₄ ≫ top = (Subcomplex.range ι₁).ι ≫ fst _ _ ≫ b :=
    ⟨sq.isPushout.desc _ _ ((Subcomplex.isInitialBot (X := W ⊗ Δ[1])).hom_ext _ _),
      sq.isPushout.inl_desc _ _ _, sq.isPushout.inr_desc _ _ _⟩
  have sq₂ : CommSq top S.ι f (fst _ _ ≫ a ≫ f) := ⟨by
    apply sq.isPushout.hom_ext
    · rw [reassoc_of% htop₀, reassoc_of% (Subcomplex.homOfLE_ι (h := sq.le₂₄))]
    · rw [reassoc_of% htop₁, reassoc_of% (Subcomplex.homOfLE_ι (h := sq.le₃₄))]
      simp [hab]⟩
  have := hf S.ι (MorphismProperty.monomorphisms.infer_property _)
  refine ⟨Homotopy.mk' sq₂.lift ?_ ?_, sq₂.fac_right⟩
  · have e : (ι₀ : W ⟶ W ⊗ Δ[1]) =
        Subcomplex.toRange ι₀ ≫ Subcomplex.homOfLE sq.le₂₄ ≫ S.ι := by
      rw [Subcomplex.homOfLE_ι, Subcomplex.toRange_ι]
    rw [e, Category.assoc, Category.assoc, sq₂.fac_left, htop₀]
    simp
  · have e : (ι₁ : W ⟶ W ⊗ Δ[1]) =
        Subcomplex.toRange ι₁ ≫ Subcomplex.homOfLE sq.le₃₄ ≫ S.ι := by
      rw [Subcomplex.homOfLE_ι, Subcomplex.toRange_ι]
    rw [e, Category.assoc, Category.assoc, sq₂.fac_left, htop₁]
    simp

end SSet
