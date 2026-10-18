/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Equivalence.KanOfEquiv
import SimplicialHomotopy.Horn.OuterHorn
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.CategoryTheory.SingleObj

/-!
# The nerve of a groupoid is a Kan complex

`nerve C` is a quasicategory for every category `C` (Mathlib, `Nerve.quasicategory`); when
`C` is a groupoid every edge of `nerve C` is an equivalence (its underlying morphism is an
isomorphism), so `SSet.kanComplex_of_isEquiv_edges` (Kerodon 019D, (d) ⇒ (b), in
`Equivalence/KanOfEquiv.lean`) together with the special outer horn theorem
`SSet.fillOuterHornOfIsEquiv` (Kerodon 019F, `Horn/OuterHorn.lean`) makes it a Kan
complex.

* `SSet.isEquiv_edgeMk_of_isIso f : (nerve.edgeMk f).IsEquiv` for an isomorphism `f` of any
  category: the inverse edge is `nerve.edgeMk (inv f)` and the two witnessing `CompStruct`s
  come from Mathlib's `nerve.nonempty_compStruct_iff`.
* `SSet.isEquiv_edge_nerve_of_groupoid e : e.IsEquiv` for every edge `e` of the nerve of a
  groupoid (via `nerve.edgeMk_surjective`).
* `SSet.kanComplex_nerve_of_groupoid C : KanComplex (nerve C)` for a groupoid `C`, registered
  as an instance; in particular `KanComplex (nerve (SingleObj (Multiplicative ℤ)))`.
-/

universe u v

open CategoryTheory

open scoped Simplicial

namespace SSet

section

variable {C : Type u} [Category.{v} C]

/-- The edge `nerve.edgeMk f` of the nerve is an equivalence when `f` is an isomorphism:
its inverse is `nerve.edgeMk (inv f)`, and the 2-simplices `mk₂ f (inv f)`, `mk₂ (inv f) f`
witness the two composition identities. -/
lemma isEquiv_edgeMk_of_isIso {x y : C} (f : x ⟶ y) [IsIso f] :
    (nerve.edgeMk f).IsEquiv := by
  obtain ⟨h₁⟩ := (nerve.nonempty_compStruct_iff f (inv f) (𝟙 x)).2 (by simp)
  obtain ⟨h₂⟩ := (nerve.nonempty_compStruct_iff (inv f) f (𝟙 y)).2 (by simp)
  exact ⟨{ inv := nerve.edgeMk (inv f)
           homInvId := h₁.ofEq rfl rfl (Edge.ext_iff.mp (nerve.edgeMk_id x))
           invHomId := h₂.ofEq rfl rfl (Edge.ext_iff.mp (nerve.edgeMk_id y)) }⟩

end

section

variable {C : Type u} [Groupoid.{v} C]

/-- Every edge of the nerve of a groupoid is an equivalence. -/
lemma isEquiv_edge_nerve_of_groupoid {x₀ x₁ : (nerve C) _⦋0⦌}
    (e : (nerve C).Edge x₀ x₁) : e.IsEquiv := by
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective x₀
  obtain ⟨y, rfl⟩ := nerveEquiv.symm.surjective x₁
  obtain ⟨f, rfl⟩ := nerve.edgeMk_surjective e
  exact isEquiv_edgeMk_of_isIso f

end

/-- The nerve of a groupoid is a Kan complex. -/
theorem kanComplex_nerve_of_groupoid (C : Type u) [Groupoid.{v} C] : KanComplex (nerve C) :=
  kanComplex_of_isEquiv_edges (nerve C) (fun e ↦ isEquiv_edge_nerve_of_groupoid e)
    fillOuterHornOfIsEquiv

instance (C : Type u) [Groupoid.{v} C] : KanComplex (nerve C) :=
  kanComplex_nerve_of_groupoid C

example : KanComplex (nerve (SingleObj (Multiplicative ℤ))) := inferInstance

end SSet
