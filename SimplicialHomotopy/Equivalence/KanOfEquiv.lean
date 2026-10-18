/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Horn.HornEdge
import SimplicialHomotopy.Equivalence.WeakEquivalence
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# A quasicategory in which every edge is an equivalence is a Kan complex

Kerodon Tag 019D (Proposition 4.4.2.1, Joyal) / [Lur09, Proposition 1.2.5.1].

* `SSet.Edge.IsEquiv e : Prop := Nonempty e.InvStruct`, with `IsEquiv.id`, `IsEquiv.map`,
  `IsEquiv.op`, and `SSet.KanComplex.isEquiv_edge`: every edge of a Kan complex is an
  equivalence.
* `SSet.FillsHorn X n i`: the horn-filling condition for `Λ[n + 1, i]` in the
  "compatible family of faces" form used by `SSet.KanComplex.iff`, with its transport
  along `X ↦ X.op` (`FillsHorn.op`, `FillsHorn.unop`) and the resulting instance
  `Quasicategory X.op`.
The initial edge `SSet.horn.edge₀₁` that `FillOuterHornOfIsEquiv` singles out lives in
`Horn/HornEdge.lean`, since `Fibration/Cocartesian.lean` needs it too.

* `SSet.FillOuterHornOfIsEquiv` (proved in `Horn/OuterHorn.lean` as
  `SSet.fillOuterHornOfIsEquiv`, re-exported as `SSet.HTT.fill_outerHorn_of_isEquiv` in
  `HTT.lean`): Joyal's
  special outer horn theorem (Kerodon Tag 019F, Theorem 4.4.2.6, (1) ⇒ (2); equivalently
  Proposition 4.4.2.13 (Tag 01H0) for `q : C ⟶ Δ[0]`):
  in a quasicategory, a horn `Λ[n + 2, 0] ⟶ C` whose initial edge `0 → 1` is an equivalence
  extends to `Δ[n + 2]`. The dual statement for `Λ[n + 2, n + 2]` is *derived* from it by
  passing to the opposite simplicial set.
* `SSet.kanComplex_of_isEquiv_edges`: Kerodon 019D, (d) ⇒ (b).
-/

universe u

open CategoryTheory Limits

open scoped Simplicial

namespace SSet

/-! ### Equivalences -/

namespace Edge

variable {X Y : SSet.{u}} {x₀ x₁ : X _⦋0⦌}

/-- An edge is an *equivalence* if it admits an `InvStruct`. -/
def IsEquiv (e : Edge x₀ x₁) : Prop := Nonempty e.InvStruct

lemma IsEquiv.id (x : X _⦋0⦌) : (Edge.id x).IsEquiv := ⟨InvStruct.invStructId x⟩

lemma IsEquiv.map {e : Edge x₀ x₁} (he : e.IsEquiv) (f : X ⟶ Y) : (e.map f).IsEquiv :=
  he.elim fun I ↦ ⟨I.map f⟩

lemma IsEquiv.inv {e : Edge x₀ x₁} (I : e.InvStruct) : I.inv.IsEquiv := ⟨I.invStructInv⟩

lemma IsEquiv.ofEq {y₀ y₁ : X _⦋0⦌} {e : Edge x₀ x₁} {e' : Edge y₀ y₁} (he : e.IsEquiv)
    (h : e.edge = e'.edge) : e'.IsEquiv :=
  he.elim fun I ↦ ⟨I.ofEq h⟩

/-! #### Opposite simplicial set -/

/-- The edge of `X.op` induced by an edge of `X` (it goes in the other direction). -/
def op (e : Edge x₀ x₁) : X.op.Edge (opObjEquiv.symm x₁) (opObjEquiv.symm x₀) :=
  Edge.mk (opObjEquiv.symm e.edge)
    (by rw [op_δ]; exact congrArg _ (by rw [show (1 : Fin 2).rev = 0 by decide]; exact e.tgt_eq))
    (by rw [op_δ]; exact congrArg _ (by rw [show (0 : Fin 2).rev = 1 by decide]; exact e.src_eq))

@[simp]
lemma op_edge (e : Edge x₀ x₁) : e.op.edge = opObjEquiv.symm e.edge := rfl

lemma op_id (x : X _⦋0⦌) : (Edge.id x).op = Edge.id (opObjEquiv.symm x) := by
  ext
  simp only [op_edge, id_edge, op_σ]
  rfl

/-- The `CompStruct` of `X.op` induced by a `CompStruct` of `X`. -/
def CompStruct.op {x₂ : X _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (c : CompStruct e₀₁ e₁₂ e₀₂) : CompStruct e₁₂.op e₀₁.op e₀₂.op :=
  CompStruct.mk (opObjEquiv.symm c.simplex)
    (by rw [op_δ]; exact congrArg _ (by rw [show (2 : Fin 3).rev = 0 by decide]; exact c.d₀))
    (by rw [op_δ]; exact congrArg _ (by rw [show (0 : Fin 3).rev = 2 by decide]; exact c.d₂))
    (by rw [op_δ]; exact congrArg _ (by rw [show (1 : Fin 3).rev = 1 by decide]; exact c.d₁))

/-- The `InvStruct` of `X.op` induced by an `InvStruct` of `X`. -/
def InvStruct.op {e : Edge x₀ x₁} (I : e.InvStruct) : e.op.InvStruct where
  inv := I.inv.op
  homInvId := I.invHomId.op.ofEq rfl rfl (by rw [op_id])
  invHomId := I.homInvId.op.ofEq rfl rfl (by rw [op_id])

lemma IsEquiv.op {e : Edge x₀ x₁} (he : e.IsEquiv) : e.op.IsEquiv :=
  he.elim fun I ↦ ⟨I.op⟩

end Edge

/-- If every edge of `X` is an equivalence, so is every edge of `X.op`. -/
lemma isEquiv_edges_op {X : SSet.{u}} (h : ∀ {x y : X _⦋0⦌} (e : X.Edge x y), e.IsEquiv)
    {x y : X.op _⦋0⦌} (e : X.op.Edge x y) : e.IsEquiv :=
  (h (Edge.mk' (opObjEquiv e.edge))).op.ofEq rfl

/-! ### Horn filling in the "family of faces" form -/

/-- `FillsHorn X n i` says that every compatible family of faces `Δ[n] ⟶ X` indexed by
`j ≠ i` (equivalently, every morphism `Λ[n + 1, i] ⟶ X`, see `fillsHorn_iff`) extends to
`Δ[n + 1] ⟶ X`. `KanComplex X ↔ ∀ n i, FillsHorn X n i` (`kanComplex_iff_fillsHorn`). -/
def FillsHorn (X : SSet.{u}) (n : ℕ) (i : Fin (n + 2)) : Prop :=
  ∀ (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ X) (_ : horn.IsCompatible f),
    ∃ (φ : Δ[n + 1] ⟶ X), ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj

lemma fillsHorn_iff (X : SSet.{u}) (n : ℕ) (i : Fin (n + 2)) :
    FillsHorn X n i ↔
      ∀ σ₀ : (Λ[n + 1, i] : SSet) ⟶ X, ∃ σ : Δ[n + 1] ⟶ X, σ₀ = Λ[n + 1, i].ι ≫ σ := by
  constructor
  · intro h σ₀
    obtain ⟨φ, hφ⟩ := h _ (horn.IsCompatible.of_hom σ₀)
    exact ⟨φ, horn.hom_ext' (fun j hj ↦ by rw [← Category.assoc, horn.ι_ι, hφ])⟩
  · intro h f hf
    obtain ⟨σ, hσ⟩ := h hf.desc
    exact ⟨σ, fun j hj ↦ by rw [← horn.ι_ι i j hj, Category.assoc, ← hσ, hf.ι_desc]⟩

lemma kanComplex_iff_fillsHorn (X : SSet.{u}) :
    KanComplex X ↔ ∀ (n : ℕ) (i : Fin (n + 2)), FillsHorn X n i :=
  KanComplex.iff

lemma fillsHorn_of_quasicategory (X : SSet.{u}) [Quasicategory X] {n : ℕ} {i : Fin (n + 2)}
    (h0 : 0 < i) (hn : i < Fin.last (n + 1)) : FillsHorn X n i :=
  (fillsHorn_iff X n i).2 fun σ₀ ↦ Quasicategory.hornFilling h0 hn σ₀

/-- Horn filling for `Λ[n + 1, i.rev]` in `X` gives horn filling for `Λ[n + 1, i]` in `X.op`
(the proof is that of Mathlib's instance `KanComplex X.op`). -/
lemma FillsHorn.op {X : SSet.{u}} {n : ℕ} {i : Fin (n + 2)} (h : FillsHorn X n i.rev) :
    FillsHorn X.op n i := by
  intro f hf
  replace hf : horn.IsCompatible (i := i.rev)
      (fun j hj ↦ yonedaEquiv.symm (opObjEquiv (yonedaEquiv (f j.rev (by grind))))) := by
    obtain _ | n := n
    · simp
    · rw [horn.isCompatible_iff]
      intro j k jh hk hjk
      simp only [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
        ← stdSimplex.yonedaEquiv_δ_comp]
      congr 3
      convert (hf.δ_pred_comp k.rev j.rev (by grind) (by grind) (by grind)).symm <;>
        grind [Fin.castPred]
  obtain ⟨φ, hφ⟩ := h _ hf
  refine ⟨yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv φ)), fun j hj ↦ ?_⟩
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ, Equiv.apply_symm_apply,
    ← stdSimplex.yonedaEquiv_δ_comp, hφ j.rev (by grind)]
  simp

/-- Horn filling for `Λ[n + 1, i.rev]` in `X.op` gives horn filling for `Λ[n + 1, i]` in `X`. -/
lemma FillsHorn.unop {X : SSet.{u}} {n : ℕ} {i : Fin (n + 2)} (h : FillsHorn X.op n i.rev) :
    FillsHorn X n i := by
  intro f hf
  replace hf : horn.IsCompatible (i := i.rev)
      (fun j hj ↦ yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv (f j.rev (by grind))))) := by
    obtain _ | n := n
    · simp
    · rw [horn.isCompatible_iff]
      intro j k jh hk hjk
      simp only [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ, Equiv.apply_symm_apply,
        ← stdSimplex.yonedaEquiv_δ_comp]
      congr 3
      convert (hf.δ_pred_comp k.rev j.rev (by grind) (by grind) (by grind)).symm <;>
        grind [Fin.castPred]
  obtain ⟨φ, hφ⟩ := h _ hf
  refine ⟨yonedaEquiv.symm (opObjEquiv (yonedaEquiv φ)), fun j hj ↦ ?_⟩
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
    ← stdSimplex.yonedaEquiv_δ_comp, hφ j.rev (by grind)]
  simp

instance quasicategory_op (X : SSet.{u}) [Quasicategory X] : Quasicategory X.op where
  hornFilling' n i σ₀ h0 hn :=
    (fillsHorn_iff _ _ _).1 (FillsHorn.op (fillsHorn_of_quasicategory X (i := i.rev)
      (by rw [Fin.lt_def] at *; simp [Fin.val_rev] at *; omega)
      (by rw [Fin.lt_def] at *; simp [Fin.val_rev] at *; omega))) σ₀


/-! ### The special outer horn theorem (Joyal) -/

/-- The statement of **Joyal's special outer horn theorem** (Kerodon Tag 019F, Theorem
4.4.2.6, (1) ⇒ (2) — equivalently Proposition 4.4.2.13 (Tag 01H0) for `q : C ⟶ Δ[0]`;
[Lur09, Proposition 1.2.5.1 / Joyal, *Quasi-categories and Kan complexes*, Theorem 2.2]): if
`C` is an ∞-category, `n ≥ 2`, and `σ₀ : Λ[n, 0] ⟶ C` is a horn
whose initial edge `0 → 1` is an equivalence, then `σ₀` extends to `Δ[n]`. It is taken as a
hypothesis below and **proved** in `Horn/OuterHorn.lean` (`SSet.fillOuterHornOfIsEquiv`,
via the last-vertex form of `Horn/OuterHornLast.lean`, which follows Kerodon's proof
through coslices over diagrams and joins). The dual statement for `Λ[n, n]` is derived from it
(`fillsHorn_last_of_isEquiv_edges`) by passing to the opposite simplicial set. -/
def FillOuterHornOfIsEquiv : Prop :=
  ∀ {C : SSet.{u}} [Quasicategory C] {n : ℕ} (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ C),
    (Edge.mk' (σ₀.app _ (horn.edge₀₁ n))).IsEquiv → ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, 0].ι ≫ σ

/-! ### Kerodon 019D -/

section

variable (C : SSet.{u}) [Quasicategory C] (h : ∀ {x y : C _⦋0⦌} (e : C.Edge x y), e.IsEquiv)
  (H : FillOuterHornOfIsEquiv.{u})

include h H in
/-- Outer horns `Λ[n + 2, 0]` can be filled in a quasicategory all of whose edges are
equivalences. -/
theorem fillsHorn_zero_of_isEquiv_edges (n : ℕ) : FillsHorn C (n + 1) 0 :=
  (fillsHorn_iff _ _ _).2 fun σ₀ ↦ H σ₀ (h _)

include h H in
/-- Outer horns `Λ[n + 2, n + 2]` can be filled in a quasicategory all of whose edges are
equivalences (derived from the `Λ[n + 2, 0]` case by passing to `C.op`). -/
theorem fillsHorn_last_of_isEquiv_edges (n : ℕ) :
    FillsHorn C (n + 1) (Fin.last (n + 2)) :=
  FillsHorn.unop (by
    rw [Fin.rev_last]
    exact fillsHorn_zero_of_isEquiv_edges C.op (fun e ↦ isEquiv_edges_op h e) H n)

include h H in
/-- **Kerodon Tag 019D** (Joyal), (d) ⇒ (b): a quasicategory in which every edge is an
equivalence is a Kan complex. -/
theorem kanComplex_of_isEquiv_edges : KanComplex C := by
  rw [kanComplex_iff_fillsHorn]
  intro n i
  obtain _ | n := n
  · -- `Λ[1, i]`: the horn is a vertex, extend by a degenerate edge.
    intro f hf
    have hi : i.rev ≠ i := fun h ↦ by
      have := congrArg Fin.val h
      simp only [Fin.val_rev] at this
      omega
    refine ⟨stdSimplex.σ 0 ≫ f i.rev hi, fun j hj ↦ ?_⟩
    obtain rfl : j = i.rev := Fin.ext (by
      have := Fin.val_ne_iff.2 hj
      simp only [Fin.val_rev]
      omega)
    rw [← Category.assoc,
      stdSimplex.isTerminalObj₀.hom_ext (stdSimplex.δ i.rev ≫ stdSimplex.σ 0) (𝟙 _),
      Category.id_comp]
  · by_cases h0 : i = 0
    · subst h0
      exact fillsHorn_zero_of_isEquiv_edges C h H n
    · by_cases hn : i = Fin.last (n + 2)
      · subst hn
        exact fillsHorn_last_of_isEquiv_edges C h H n
      · exact fillsHorn_of_quasicategory C ((Fin.pos_iff_ne_zero' i).2 h0)
          (Fin.lt_last_iff_ne_last.2 hn)

end

/-! ### Every edge of a Kan complex is an equivalence -/

namespace KanComplex

variable {X : SSet.{u}} [KanComplex X]

/-- `Λ[2, 0]`-filling in a Kan complex, keeping the `2`-simplex: given edges
`e₀₁ : x₀ → x₁` and `e₀₂ : x₀ → x₂`, there is an edge `e₁₂ : x₁ → x₂` together with a
`2`-simplex witnessing `e₀₂ = e₁₂ ∘ e₀₁`. -/
lemma exists_compStruct_of_edges {x₀ x₁ x₂ : X _⦋0⦌} (e₀₁ : X.Edge x₀ x₁)
    (e₀₂ : X.Edge x₀ x₂) :
    ∃ (e₁₂ : X.Edge x₁ x₂), Nonempty (Edge.CompStruct e₀₁ e₁₂ e₀₂) := by
  let F : ∀ (j : Fin 3) (_ : j ≠ 0), Δ[1] ⟶ X :=
    fun j _ ↦ if j = 1 then yonedaEquiv.symm e₀₂.edge else yonedaEquiv.symm e₀₁.edge
  have hF : horn.IsCompatible F := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk
    change stdSimplex.δ 1 ≫ yonedaEquiv.symm e₀₂.edge =
      stdSimplex.δ 1 ≫ yonedaEquiv.symm e₀₁.edge
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
      e₀₂.src_eq, e₀₁.src_eq]
  obtain ⟨φ, hφ⟩ := hF.exists_lift_of_kanComplex
  have h2 : X.δ 2 (yonedaEquiv φ) = e₀₁.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hφ 2 (by decide)]
    simp [F]
  have h1 : X.δ 1 (yonedaEquiv φ) = e₀₂.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hφ 1 (by decide)]
    simp [F]
  refine ⟨Edge.mk (X.δ 0 (yonedaEquiv φ)) ?_ ?_, ⟨Edge.CompStruct.mk (yonedaEquiv φ) h2 rfl h1⟩⟩
  · have := X.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) (yonedaEquiv φ)
    simp only [Fin.castSucc_zero, Fin.succ_one_eq_two] at this
    rw [← this, h2, e₀₁.tgt_eq]
  · have := X.δ_comp_δ_self_apply (i := (0 : Fin 2)) (yonedaEquiv φ)
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at this
    rw [this, h1, e₀₂.tgt_eq]

/-- Every edge of a Kan complex admits an `InvStruct`: a right inverse `inv` is obtained by
`Λ[2, 0]`-filling, and a `Λ[3, 3]`-filling with faces `(homInvId, σ₀ inv, σ₁ inv, •)` shows
that `inv` is also a left inverse (Kerodon 019F, (3) ⇒ (1)). -/
lemma exists_invStruct {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) : Nonempty e.InvStruct := by
  obtain ⟨inv, ⟨α⟩⟩ := exists_compStruct_of_edges e (Edge.id x₀)
  let G : ∀ (j : Fin 4) (_ : j ≠ 3), Δ[2] ⟶ X := fun j _ ↦
    if j = 0 then yonedaEquiv.symm α.simplex
    else if j = 1 then yonedaEquiv.symm (X.σ 0 inv.edge)
    else yonedaEquiv.symm (X.σ 1 inv.edge)
  have hG : horn.IsCompatible G := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk
    · change stdSimplex.δ 0 ≫ yonedaEquiv.symm α.simplex =
        stdSimplex.δ 0 ≫ yonedaEquiv.symm (X.σ 0 inv.edge)
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, α.d₀,
        X.δ_comp_σ_self'_apply (i := 0) (by decide)]
    · change stdSimplex.δ 1 ≫ yonedaEquiv.symm α.simplex =
        stdSimplex.δ 0 ≫ yonedaEquiv.symm (X.σ 1 inv.edge)
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, α.d₁]
      have := X.δ_comp_σ_of_le_apply (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide) inv.edge
      rw [show Fin.castSucc (0 : Fin 2) = 0 by decide, show Fin.succ (0 : Fin 1) = 1 by decide,
        inv.tgt_eq] at this
      rw [this]
      rfl
    · change stdSimplex.δ 1 ≫ yonedaEquiv.symm (X.σ 0 inv.edge) =
        stdSimplex.δ 1 ≫ yonedaEquiv.symm (X.σ 1 inv.edge)
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
        X.δ_comp_σ_succ'_apply (i := 0) (by decide), X.δ_comp_σ_self'_apply (i := 1) (by decide)]
  obtain ⟨φ, hφ⟩ := hG.exists_lift_of_kanComplex
  have h0 : X.δ 0 (yonedaEquiv φ) = α.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hφ 0 (by decide)]
    simp [G]
  have h1 : X.δ 1 (yonedaEquiv φ) = X.σ 0 inv.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hφ 1 (by decide)]
    simp [G]
  have h2 : X.δ 2 (yonedaEquiv φ) = X.σ 1 inv.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hφ 2 (by decide)]
    simp [G]
  refine ⟨⟨inv, α, Edge.CompStruct.mk (X.δ 3 (yonedaEquiv φ)) ?_ ?_ ?_⟩⟩
  · have := X.δ_comp_δ_self_apply (i := (2 : Fin 3)) (yonedaEquiv φ)
    rw [show Fin.castSucc (2 : Fin 3) = 2 by decide, show Fin.succ (2 : Fin 3) = 3 by decide]
      at this
    rw [← this, h2, X.δ_comp_σ_succ'_apply (i := 1) (by decide)]
  · have := X.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) (yonedaEquiv φ)
    rw [show Fin.castSucc (0 : Fin 3) = 0 by decide, show Fin.succ (2 : Fin 3) = 3 by decide]
      at this
    rw [this, h0, α.d₂]
  · have := X.δ_comp_δ_apply (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) (yonedaEquiv φ)
    rw [show Fin.castSucc (1 : Fin 3) = 1 by decide, show Fin.succ (2 : Fin 3) = 3 by decide]
      at this
    rw [this, h1]
    have := X.δ_comp_σ_of_gt_apply (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) inv.edge
    rw [show Fin.castSucc (0 : Fin 1) = 0 by decide, show Fin.succ (1 : Fin 2) = 2 by decide,
      inv.src_eq] at this
    rw [this]
    rfl

/-- Every edge of a Kan complex is an equivalence. -/
lemma isEquiv_edge {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) : e.IsEquiv :=
  exists_invStruct e

end KanComplex

end SSet
