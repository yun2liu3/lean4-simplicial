/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Equivalence.Equivalences
import SimplicialHomotopy.Fibration.RightFibrations

/-!
# Left and right fibrations are conservative

Kerodon Tag 019K (Proposition 4.4.2.11): if `q : X ⟶ Y` is a left or right fibration between
quasicategories and `e` is an edge of `X` whose image `q(e)` is an equivalence of `Y`, then `e`
is already an equivalence of `X`.

This is the first step of Kerodon's proof of the special outer horn theorem
(Tag 019F = Theorem 4.4.2.6, which `Cofinal/HTT.lean` re-exports as
`SSet.HTT.fill_outerHorn_of_isEquiv`): 019F follows from Proposition 4.4.2.13 (Tag 01H0), whose
proof produces a lifting problem in a fibre product of coslices and solves it by observing that
the relevant edge is an isomorphism *because* the left fibration `θ` is conservative. Nothing
here is assumed; the file is `sorry`-free.

The key input is relative horn filling, in the two forms that a one-sided fibration provides:

* `SSet.exists_compStruct_of_leftFibration` : `Λ[2, 0]`-filling relative to a left fibration —
  given edges `e₀₁ : x₀ → x₁`, `e₀₂ : x₀ → x₂` of `X` and a `2`-simplex of `Y` exhibiting
  `q(e₀₂)` as a composite `_ ∘ q(e₀₁)`, there is an edge `e₁₂ : x₁ → x₂` of `X` and a
  `2`-simplex of `X` over the given one exhibiting `e₀₂` as `e₁₂ ∘ e₀₁`.
* `SSet.exists_compStruct_of_rightFibration` : the mirror statement for `Λ[2, 2]`.

From either of these, applied twice, one gets a two-sided inverse in the homotopy category and
hence an `InvStruct` by `SimplicialHomotopy.isEquiv_of_isIso_homMk`:

* `SimplicialHomotopy.isEquiv_of_leftFibration`, `SimplicialHomotopy.isEquiv_of_rightFibration` :
  **Kerodon 019K**.
* `SimplicialHomotopy.isEquiv_map_iff_of_leftFibration`,
  `SimplicialHomotopy.isEquiv_map_iff_of_rightFibration` :
  the resulting `iff` (the other direction is `SSet.Edge.IsEquiv.map`, true for any morphism).
-/

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty

open scoped Simplicial

namespace SSet

variable {X Y : SSet.{u}}

/-! ### Relative horn filling along a one-sided fibration -/

/-- `Λ[2, 0]`-filling relative to a left fibration `q`: given edges `e₀₁ : x₀ → x₁` and
`e₀₂ : x₀ → x₂` of `X`, and a `2`-simplex `β` of `Y` whose `2`nd face is `q(e₀₁)` and whose
`1`st face is `q(e₀₂)`, there is an edge `e₁₂ : x₁ → x₂` lying over the `0`th face of `β`
together with a `CompStruct` exhibiting `e₀₂` as `e₁₂ ∘ e₀₁`. -/
lemma exists_compStruct_of_leftFibration (q : X ⟶ Y) [LeftFibration q]
    {x₀ x₁ x₂ : X _⦋0⦌} (e₀₁ : X.Edge x₀ x₁) (e₀₂ : X.Edge x₀ x₂) (β : Y _⦋2⦌)
    (hd₂ : Y.δ 2 β = q.app _ e₀₁.edge) (hd₁ : Y.δ 1 β = q.app _ e₀₂.edge) :
    ∃ (e₁₂ : X.Edge x₁ x₂) (_ : Edge.CompStruct e₀₁ e₁₂ e₀₂),
      q.app _ e₁₂.edge = Y.δ 0 β := by
  let F : ∀ (j : Fin 3) (_ : j ≠ 0), Δ[1] ⟶ X :=
    fun j _ ↦ if j = 1 then yonedaEquiv.symm e₀₂.edge else yonedaEquiv.symm e₀₁.edge
  have hF : horn.IsCompatible F := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk
    change stdSimplex.δ 1 ≫ yonedaEquiv.symm e₀₂.edge =
      stdSimplex.δ 1 ≫ yonedaEquiv.symm e₀₁.edge
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
      e₀₂.src_eq, e₀₁.src_eq]
  have hcomm : hF.desc ≫ q = Λ[2, 0].ι ≫ yonedaEquiv.symm β := by
    refine horn.hom_ext' (fun j hj ↦ ?_)
    rw [← Category.assoc, hF.ι_desc j hj, ← Category.assoc, horn.ι_ι]
    fin_cases j
    · simp at hj
    · show yonedaEquiv.symm e₀₂.edge ≫ q = stdSimplex.δ 1 ≫ yonedaEquiv.symm β
      rw [yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, hd₁]
    · show yonedaEquiv.symm e₀₁.edge ≫ q = stdSimplex.δ 2 ≫ yonedaEquiv.symm β
      rw [yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, hd₂]
  have : HasLiftingProperty (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι q :=
    mem_leftFibrations q _ (horn_ι_mem_leftHornInclusions (n := 2) (i := 0) (by decide))
  have sq : CommSq hF.desc Λ[2, 0].ι q (yonedaEquiv.symm β) := ⟨hcomm⟩
  have h2 : X.δ 2 (yonedaEquiv sq.lift) = e₀₁.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι (i := 0) (j := 2) (by decide),
      Category.assoc, sq.fac_left, hF.ι_desc]
    simp [F]
  have h1 : X.δ 1 (yonedaEquiv sq.lift) = e₀₂.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι (i := 0) (j := 1) (by decide),
      Category.assoc, sq.fac_left, hF.ι_desc]
    simp [F]
  have hq : q.app _ (yonedaEquiv sq.lift) = β := by
    rw [← yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]
  refine ⟨Edge.mk (X.δ 0 (yonedaEquiv sq.lift)) ?_ ?_,
    Edge.CompStruct.mk (yonedaEquiv sq.lift) h2 rfl h1, ?_⟩
  · have := X.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
      (yonedaEquiv sq.lift)
    simp only [Fin.castSucc_zero, Fin.succ_one_eq_two] at this
    rw [← this, h2, e₀₁.tgt_eq]
  · have := X.δ_comp_δ_self_apply (i := (0 : Fin 2)) (yonedaEquiv sq.lift)
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at this
    rw [this, h1, e₀₂.tgt_eq]
  · show q.app _ (X.δ 0 (yonedaEquiv sq.lift)) = Y.δ 0 β
    conv_rhs => rw [← hq]
    simp [SimplicialObject.δ]

/-- `Λ[2, 2]`-filling relative to a right fibration `q`: given edges `e₁₂ : x₁ → x₂` and
`e₀₂ : x₀ → x₂` of `X`, and a `2`-simplex `β` of `Y` whose `0`th face is `q(e₁₂)` and whose
`1`st face is `q(e₀₂)`, there is an edge `e₀₁ : x₀ → x₁` lying over the `2`nd face of `β`
together with a `CompStruct` exhibiting `e₀₂` as `e₁₂ ∘ e₀₁`. -/
lemma exists_compStruct_of_rightFibration (q : X ⟶ Y) [RightFibration q]
    {x₀ x₁ x₂ : X _⦋0⦌} (e₁₂ : X.Edge x₁ x₂) (e₀₂ : X.Edge x₀ x₂) (β : Y _⦋2⦌)
    (hd₀ : Y.δ 0 β = q.app _ e₁₂.edge) (hd₁ : Y.δ 1 β = q.app _ e₀₂.edge) :
    ∃ (e₀₁ : X.Edge x₀ x₁) (_ : Edge.CompStruct e₀₁ e₁₂ e₀₂),
      q.app _ e₀₁.edge = Y.δ 2 β := by
  let F : ∀ (j : Fin 3) (_ : j ≠ 2), Δ[1] ⟶ X :=
    fun j _ ↦ if j = 0 then yonedaEquiv.symm e₁₂.edge else yonedaEquiv.symm e₀₂.edge
  have hF : horn.IsCompatible F := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk
    change stdSimplex.δ 0 ≫ yonedaEquiv.symm e₁₂.edge =
      stdSimplex.δ 0 ≫ yonedaEquiv.symm e₀₂.edge
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
      e₁₂.tgt_eq, e₀₂.tgt_eq]
  have hcomm : hF.desc ≫ q = Λ[2, 2].ι ≫ yonedaEquiv.symm β := by
    refine horn.hom_ext' (fun j hj ↦ ?_)
    rw [← Category.assoc, hF.ι_desc j hj, ← Category.assoc, horn.ι_ι]
    fin_cases j
    · show yonedaEquiv.symm e₁₂.edge ≫ q = stdSimplex.δ 0 ≫ yonedaEquiv.symm β
      rw [yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, hd₀]
    · show yonedaEquiv.symm e₀₂.edge ≫ q = stdSimplex.δ 1 ≫ yonedaEquiv.symm β
      rw [yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, hd₁]
    · simp at hj
  have : HasLiftingProperty (Λ[2, 2] : (Δ[2] : SSet.{u}).Subcomplex).ι q :=
    mem_rightFibrations q _ (horn_ι_mem_rightHornInclusions (n := 2) (i := 2) (by decide))
  have sq : CommSq hF.desc Λ[2, 2].ι q (yonedaEquiv.symm β) := ⟨hcomm⟩
  have h0 : X.δ 0 (yonedaEquiv sq.lift) = e₁₂.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι (i := 2) (j := 0) (by decide),
      Category.assoc, sq.fac_left, hF.ι_desc]
    simp [F]
  have h1 : X.δ 1 (yonedaEquiv sq.lift) = e₀₂.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι (i := 2) (j := 1) (by decide),
      Category.assoc, sq.fac_left, hF.ι_desc]
    simp [F]
  have hq : q.app _ (yonedaEquiv sq.lift) = β := by
    rw [← yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]
  refine ⟨Edge.mk (X.δ 2 (yonedaEquiv sq.lift)) ?_ ?_,
    Edge.CompStruct.mk (yonedaEquiv sq.lift) rfl h0 h1, ?_⟩
  · have := X.δ_comp_δ_apply (i := (1 : Fin 2)) (j := (1 : Fin 2)) (le_refl _)
      (yonedaEquiv sq.lift)
    simp only [Fin.castSucc_one, Fin.succ_one_eq_two] at this
    rw [this, h1, e₀₂.src_eq]
  · have := X.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
      (yonedaEquiv sq.lift)
    simp only [Fin.castSucc_zero, Fin.succ_one_eq_two] at this
    rw [this, h0, e₁₂.src_eq]
  · show q.app _ (X.δ 2 (yonedaEquiv sq.lift)) = Y.δ 2 β
    conv_rhs => rw [← hq]
    simp [SimplicialObject.δ]

end SSet

namespace SimplicialHomotopy

open Simplicial SSet SSet.HomotopyCategory

variable {X Y : SSet.{u}}

/-- If `f ≫ g = 𝟙` and `g ≫ h = 𝟙` then `g` is a two-sided inverse of `f`. -/
private lemma isIso_of_comp_eq_id_of_comp_eq_id {C : Type*} [Category C] {a b : C}
    {f : a ⟶ b} {g : b ⟶ a} {h : a ⟶ b} (hfg : f ≫ g = 𝟙 a) (hgh : g ≫ h = 𝟙 b) :
    IsIso f := by
  refine ⟨g, hfg, ?_⟩
  calc g ≫ f = g ≫ f ≫ (g ≫ h) := by rw [hgh, Category.comp_id]
    _ = (g ≫ (f ≫ g)) ≫ h := by simp
    _ = g ≫ h := by rw [hfg, Category.comp_id]
    _ = 𝟙 b := hgh

/-- If `g ≫ f = 𝟙` and `h ≫ g = 𝟙` then `g` is a two-sided inverse of `f`. -/
private lemma isIso_of_comp_eq_id_of_comp_eq_id' {C : Type*} [Category C] {a b : C}
    {f : a ⟶ b} {g : b ⟶ a} {h : a ⟶ b} (hgf : g ≫ f = 𝟙 b) (hhg : h ≫ g = 𝟙 a) :
    IsIso f := by
  refine ⟨g, ?_, hgf⟩
  calc f ≫ g = ((h ≫ g) ≫ f) ≫ g := by rw [hhg, Category.id_comp]
    _ = h ≫ (g ≫ f) ≫ g := by simp
    _ = h ≫ g := by rw [hgf, Category.id_comp]
    _ = 𝟙 a := hhg

/-- **Kerodon Tag 019K** (Proposition 4.4.2.11): a left fibration between quasicategories is
conservative. -/
lemma isEquiv_of_leftFibration (q : X ⟶ Y) [Quasicategory X] [LeftFibration q]
    {x₀ x₁ : X _⦋0⦌} {e : X.Edge x₀ x₁} (he : (e.map q).IsEquiv) : e.IsEquiv := by
  obtain ⟨J⟩ := he
  -- a right inverse `v` of `e`, lying over `J.inv`
  obtain ⟨v, α, hv⟩ := exists_compStruct_of_leftFibration q e (Edge.id x₀) J.homInvId.simplex
    J.homInvId.d₂ (by rw [J.homInvId.d₁]; simp [SimplicialObject.σ])
  have hvq : (v.map q).IsEquiv :=
    (Edge.IsEquiv.inv J).ofEq (by rw [Edge.map_edge, hv, J.homInvId.d₀])
  obtain ⟨K⟩ := hvq
  -- a right inverse `w` of `v`
  obtain ⟨w, γ, -⟩ := exists_compStruct_of_leftFibration q v (Edge.id x₁) K.homInvId.simplex
    K.homInvId.d₂ (by rw [K.homInvId.d₁]; simp [SimplicialObject.σ])
  have h₁ : homMk e ≫ homMk v = 𝟙 (HomotopyCategory.mk x₀) := by
    rw [homMk_comp_homMk α, homMk_id]
  have h₂ : homMk v ≫ homMk w = 𝟙 (HomotopyCategory.mk x₁) := by
    rw [homMk_comp_homMk γ, homMk_id]
  have := isIso_of_comp_eq_id_of_comp_eq_id h₁ h₂
  exact isEquiv_of_isIso_homMk e

/-- **Kerodon Tag 019K** (Proposition 4.4.2.11): a right fibration between quasicategories is
conservative. -/
lemma isEquiv_of_rightFibration (q : X ⟶ Y) [Quasicategory X] [RightFibration q]
    {x₀ x₁ : X _⦋0⦌} {e : X.Edge x₀ x₁} (he : (e.map q).IsEquiv) : e.IsEquiv := by
  obtain ⟨J⟩ := he
  -- a left inverse `v` of `e`, lying over `J.invHomId`'s inverse edge
  obtain ⟨v, α, hv⟩ := exists_compStruct_of_rightFibration q e (Edge.id x₁) J.invHomId.simplex
    J.invHomId.d₀ (by rw [J.invHomId.d₁]; simp [SimplicialObject.σ])
  have hvq : (v.map q).IsEquiv :=
    (Edge.IsEquiv.inv J).ofEq (by rw [Edge.map_edge, hv, J.invHomId.d₂])
  obtain ⟨K⟩ := hvq
  -- a left inverse `w` of `v`
  obtain ⟨w, γ, -⟩ := exists_compStruct_of_rightFibration q v (Edge.id x₀) K.invHomId.simplex
    K.invHomId.d₀ (by rw [K.invHomId.d₁]; simp [SimplicialObject.σ])
  have h₁ : homMk v ≫ homMk e = 𝟙 (HomotopyCategory.mk x₁) := by
    rw [homMk_comp_homMk α, homMk_id]
  have h₂ : homMk w ≫ homMk v = 𝟙 (HomotopyCategory.mk x₀) := by
    rw [homMk_comp_homMk γ, homMk_id]
  have := isIso_of_comp_eq_id_of_comp_eq_id' h₁ h₂
  exact isEquiv_of_isIso_homMk e

/-- An edge of the source of a left fibration between quasicategories is an equivalence iff its
image is (Kerodon 019K). -/
lemma isEquiv_map_iff_of_leftFibration (q : X ⟶ Y) [Quasicategory X] [LeftFibration q]
    {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) : (e.map q).IsEquiv ↔ e.IsEquiv :=
  ⟨isEquiv_of_leftFibration q, fun he ↦ he.map q⟩

/-- An edge of the source of a right fibration between quasicategories is an equivalence iff its
image is (Kerodon 019K). -/
lemma isEquiv_map_iff_of_rightFibration (q : X ⟶ Y) [Quasicategory X] [RightFibration q]
    {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) : (e.map q).IsEquiv ↔ e.IsEquiv :=
  ⟨isEquiv_of_rightFibration q, fun he ↦ he.map q⟩

end SimplicialHomotopy
