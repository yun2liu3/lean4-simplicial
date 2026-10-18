/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Horn.HornEdge
import SimplicialHomotopy.Fibration.LeftFibrations

/-!
# Cocartesian edges and cocartesian fibrations of simplicial sets

Mathlib has `SSet.innerFibrations`, and this library adds `SSet.leftFibrations`
(`Fibration/LeftFibrations.lean`); neither had the *cocartesian* notions.
This file introduces them.

* `SSet.IsCocartesianEdge p e` (Kerodon Tag 01T5, Definition 5.1.1.1; [Lur09, 2.4.1.1] states
  the equivalent trivial-fibration form): the `1`-simplex `e` of `X` is **`p`-cocartesian** if
  every lifting problem

  ```
  Λ[n + 2, 0] --σ₀--> X
      |               |
      ι               p
      v               v
    Δ[n + 2] ---τ---> S
  ```

  whose initial edge `σ₀(0 → 1)` is `e` admits a solution. Note the shape: this is the *outer*
  horn `Λ[n, 0]`, and the constraint is only on the edge `0 → 1`, so the condition is the
  left-fibration lifting property restricted to horns with a prescribed initial edge.
* `SSet.cocartesianFibrations` / `SSet.CocartesianFibration` (Kerodon Tag 01UA,
  Definition 5.1.4.1; [Lur09, 2.4.2.1]): an inner fibration `p : X ⟶ S` such that every edge
  `f` of `S` whose source is hit by a vertex `x` of `X` lifts to a `p`-cocartesian edge of `X`
  with source `x`.

Along the way, `SSet.hornOneZeroIso : Δ[0] ≅ Λ[1, 0]` identifies the outer horn `Λ[1, 0]` with
the initial vertex of `Δ[1]`; that is what lets Kerodon's vertex-and-edge phrasing of 01UA be
matched up with the lifting problem for the left horn inclusion `Λ[1, 0].ι`.

The two results proved here:

* `SSet.isCocartesianEdge_of_leftFibration` — if `p` is a left fibration then **every** edge of
  `X` is `p`-cocartesian, since the defining lifting problem is a left-horn lifting problem with
  its initial-edge constraint simply discarded;
* `SSet.leftFibrations_le_cocartesianFibrations` — a left fibration is a cocartesian fibration
  ([Lur09, 2.4.2.4] in the direction that needs no input), hence so is every Kan fibration.

## What is deliberately not here

The two theorems of [Lur09, §2.4.1] that need Joyal's machinery — that a degenerate edge is
`p`-cocartesian for any inner fibration `p` (Kerodon Tag 01TB), and that over `Δ[0]` the
`p`-cocartesian edges are exactly the equivalences (Kerodon Tag 01T8) — are not stated in this
library and not used; see the `TODO` at the end.
-/

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty

open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

variable {X S : SSet.{u}}

/-! ### Cocartesian edges -/

/-- **Kerodon Tag 01T5** (Definition 5.1.1.1) / [Lur09, Definition 2.4.1.1]: a `1`-simplex `e`
of `X` is **`p`-cocartesian** if every outer-horn lifting problem against `p` whose initial edge
`0 → 1` is `e` has a solution. -/
def IsCocartesianEdge (p : X ⟶ S) (e : X _⦋1⦌) : Prop :=
  ∀ {n : ℕ} (σ₀ : (Λ[n + 2, 0] : SSet.{u}) ⟶ X) (τ : Δ[n + 2] ⟶ S),
    σ₀ ≫ p = Λ[n + 2, 0].ι ≫ τ → σ₀.app _ (horn.edge₀₁ n) = e →
    ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, 0].ι ≫ σ = σ₀ ∧ σ ≫ p = τ

/-- Being `p`-cocartesian depends only on the underlying `1`-simplex, so it transports along an
equality of `1`-simplices. -/
lemma IsCocartesianEdge.of_eq {p : X ⟶ S} {e e' : X _⦋1⦌} (h : IsCocartesianEdge p e)
    (he : e = e') : IsCocartesianEdge p e' := by
  subst he; exact h

/-- An edge of `X`, in the sense of `SSet.Edge`, is `p`-cocartesian if its underlying
`1`-simplex is. -/
abbrev Edge.IsCocartesian {x₀ x₁ : X _⦋0⦌} (p : X ⟶ S) (e : X.Edge x₀ x₁) : Prop :=
  IsCocartesianEdge p e.edge

/-- If `p` is a left fibration, **every** edge of `X` is `p`-cocartesian: the defining lifting
problem of `IsCocartesianEdge` is a lifting problem for the left horn inclusion
`Λ[n + 2, 0].ι`, and the constraint on the initial edge is simply not used. -/
lemma isCocartesianEdge_of_leftFibration (p : X ⟶ S) [LeftFibration p] (e : X _⦋1⦌) :
    IsCocartesianEdge p e := by
  intro n σ₀ τ w _
  have h : HasLiftingProperty Λ[n + 2, 0].ι p :=
    mem_leftFibrations p _
      (horn_ι_mem_leftHornInclusions (n := n + 2) (i := 0) (by simp [Fin.lt_def]))
  have sq : CommSq σ₀ Λ[n + 2, 0].ι p τ := ⟨w⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-! ### `Λ[1, 0]` is the initial vertex of `Δ[1]` -/

/-- `Λ[1, 0]` is the initial vertex of `Δ[1]`. Together with `hornOneZeroIso_hom_ι` this says
that a map `Λ[1, 0] ⟶ X` is the same thing as a vertex of `X`, and that the square it sits in
over `Δ[1] ⟶ S` is the same thing as the equation `S.δ 1 f = p x`. -/
noncomputable def hornOneZeroIso : Δ[0] ≅ (Λ[1, 0] : SSet.{u}) where
  hom := (stdSimplex.faceSingletonIso (0 : Fin 2)).hom ≫
    Subcomplex.homOfLE (le_of_eq horn_one_zero_eq_face.symm)
  inv := Subcomplex.homOfLE (le_of_eq horn_one_zero_eq_face.{u}) ≫
    (stdSimplex.faceSingletonIso (0 : Fin 2)).inv
  hom_inv_id := stdSimplex.isTerminalObj₀.hom_ext _ _
  inv_hom_id := by
    rw [← cancel_mono (Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).ι]
    simp

@[reassoc (attr := simp)]
lemma hornOneZeroIso_hom_ι :
    hornOneZeroIso.{u}.hom ≫ Λ[1, 0].ι = stdSimplex.δ 1 := by
  simp [hornOneZeroIso, stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]

/-! ### Cocartesian fibrations -/

/-- **Kerodon Tag 01UA** (Definition 5.1.4.1) / [Lur09, Definition 2.4.2.1]: `p : X ⟶ S` is a
**cocartesian fibration** if it is an inner fibration and for every edge `f` of `S` and every
vertex `x` of `X` above the source of `f`, there is a `p`-cocartesian edge of `X` with source
`x` lying over `f`. -/
def cocartesianFibrations : MorphismProperty SSet.{u} := fun X S p ↦
  innerFibrations p ∧
    ∀ (x : X _⦋0⦌) (f : S _⦋1⦌), S.δ 1 f = p.app _ x →
      ∃ e : X _⦋1⦌, X.δ 1 e = x ∧ p.app _ e = f ∧ IsCocartesianEdge p e

/-- A morphism `p` satisfies `[CocartesianFibration p]` if it belongs to
`cocartesianFibrations`. -/
@[mk_iff]
class CocartesianFibration (p : X ⟶ S) : Prop where
  mem : cocartesianFibrations p

lemma mem_cocartesianFibrations (p : X ⟶ S) [CocartesianFibration p] :
    cocartesianFibrations p := CocartesianFibration.mem

lemma cocartesianFibrations_le_innerFibrations :
    cocartesianFibrations.{u} ≤ innerFibrations :=
  fun _ _ _ h ↦ h.1

instance (p : X ⟶ S) [CocartesianFibration p] : InnerFibration p :=
  ⟨(mem_cocartesianFibrations p).1⟩

/-- The defining property of a cocartesian fibration: cocartesian lifts of edges exist. -/
lemma CocartesianFibration.exists_isCocartesianEdge (p : X ⟶ S) [CocartesianFibration p]
    (x : X _⦋0⦌) (f : S _⦋1⦌) (hf : S.δ 1 f = p.app _ x) :
    ∃ e : X _⦋1⦌, X.δ 1 e = x ∧ p.app _ e = f ∧ IsCocartesianEdge p e :=
  (mem_cocartesianFibrations p).2 x f hf

/-- The same statement as a solution to a lifting problem for the left horn inclusion
`Λ[1, 0].ι`, which is the form in which the definition gets used against `HasLiftingProperty`.
It is equivalent to `CocartesianFibration.exists_isCocartesianEdge` via `hornOneZeroIso`. -/
lemma CocartesianFibration.exists_lift (p : X ⟶ S) [CocartesianFibration p]
    (a : (Λ[1, 0] : SSet.{u}) ⟶ X) (b : Δ[1] ⟶ S) (w : a ≫ p = Λ[1, 0].ι ≫ b) :
    ∃ σ : Δ[1] ⟶ X, Λ[1, 0].ι ≫ σ = a ∧ σ ≫ p = b ∧
      IsCocartesianEdge p (yonedaEquiv σ) := by
  obtain ⟨e, hδ, hp, he⟩ := CocartesianFibration.exists_isCocartesianEdge p
    (yonedaEquiv (hornOneZeroIso.hom ≫ a)) (yonedaEquiv b) (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← hornOneZeroIso_hom_ι_assoc, ← w,
        ← yonedaEquiv_comp, Category.assoc])
  refine ⟨yonedaEquiv.symm e, ?_, ?_, ?_⟩
  · rw [← cancel_epi hornOneZeroIso.hom, hornOneZeroIso_hom_ι_assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm, hδ, Equiv.symm_apply_apply]
  · rw [← yonedaEquiv.injective.eq_iff, yonedaEquiv_comp, Equiv.apply_symm_apply, hp]
  · rw [Equiv.apply_symm_apply]
    exact he

/-- **A left fibration is a cocartesian fibration** ([Lur09, 2.4.2.4] in the direction that needs
no hypothesis): the lifts exist because `Λ[1, 0].ι` is a left horn inclusion, and they are
cocartesian because for a left fibration *every* edge is
(`isCocartesianEdge_of_leftFibration`). -/
lemma leftFibrations_le_cocartesianFibrations :
    leftFibrations.{u} ≤ cocartesianFibrations := by
  intro X S p hp
  have : LeftFibration p := ⟨hp⟩
  refine ⟨leftFibrations_le_innerFibrations _ hp, fun x f hf ↦ ?_⟩
  have h : HasLiftingProperty (Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).ι p :=
    mem_leftFibrations p _ (horn_ι_mem_leftHornInclusions (n := 1) (i := 0) (by decide))
  have sq : CommSq (hornOneZeroIso.inv ≫ yonedaEquiv.symm x) Λ[1, 0].ι p
      (yonedaEquiv.symm f) := ⟨by
    rw [← cancel_epi hornOneZeroIso.hom]
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, hf]⟩
  refine ⟨yonedaEquiv sq.lift, ?_, ?_, isCocartesianEdge_of_leftFibration p _⟩
  · rw [← stdSimplex.yonedaEquiv_δ_comp, ← hornOneZeroIso_hom_ι_assoc, sq.fac_left,
      Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  · rw [← yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]

instance (p : X ⟶ S) [LeftFibration p] : CocartesianFibration p :=
  ⟨leftFibrations_le_cocartesianFibrations _ (mem_leftFibrations p)⟩

/-- A Kan fibration is a cocartesian fibration. -/
lemma fibrations_le_cocartesianFibrations :
    fibrations SSet.{u} ≤ cocartesianFibrations :=
  fibrations_le_leftFibrations.trans leftFibrations_le_cocartesianFibrations

/-! ### TODO

Two facts of [Lur09, §2.4.1] that are not stated in this library:

* Kerodon Tag 01TB (Proposition 5.1.1.9, for isomorphisms): for an inner fibration `p`, every
  *degenerate* edge of `X` is `p`-cocartesian. With it, `innerFibrations p` for `p : X ⟶ Δ[0]`
  would already give `cocartesianFibrations p`, i.e. every quasicategory is cocartesian-fibred
  over the point.
* Kerodon Tag 01T8 (Example 5.1.1.4): for `p : X ⟶ Δ[0]` with `X` a quasicategory, the
  `p`-cocartesian edges are exactly the equivalences. This is what would identify
  `IsCocartesianEdge` with `Edge.IsEquiv` (`Equivalence/KanOfEquiv.lean`) in the absolute case.
  The implication from equivalences to cocartesian edges is `SSet.fillOuterHornOfIsEquiv`
  (`Horn/OuterHorn.lean`), which is not restated with `IsCocartesianEdge`.

Nothing above needs them.
-/

end SSet
