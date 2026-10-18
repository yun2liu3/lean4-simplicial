/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.Conservative
import SimplicialHomotopy.Fibration.Cocartesian

/-!
# Left fibrations are isofibrations

Kerodon Tag 01EW (Example 4.4.1.11): a left fibration `q : X ⟶ Y` is an isofibration, i.e.
every equivalence `ū : y₀ → y₁` of `Y` whose target is the image of a vertex `v` of `X` lifts
to an edge `v' → v` of `X`. (Kerodon states it for *all* equivalences of `Y`; only the lifting
against a prescribed *target* is nontrivial for a left fibration, since lifting against a
prescribed source is the definition.)

* `SSet.exists_edge_of_leftFibration` : the lift, from an `InvStruct` of `ū`.
* `SSet.exists_edge_of_leftFibration_of_isEquiv` : the same from `ū.IsEquiv`.

This is the step of Kerodon's proof of Proposition 4.4.2.13 (Tag 01H0) that solves the lifting
problem in the coslice: there the equivalence lives in `X_{f₀/}` and the left fibration is the
restriction `X_{f/} ⟶ X_{f₀/}` of `Slice/CosliceFibration.lean`.

The proof is two horn fillings against `q`: the inverse `ū⁻¹ : y₁ → y₀` lifts to an edge
`w : v → v'` because `q` has the right lifting property against `Λ[1, 0].ι`
(`SSet.CocartesianFibration.exists_isCocartesianEdge` for the cocartesian fibration `q`), and
then the `2`-simplex of `Y` witnessing `ū ∘ ū⁻¹ ≃ id` lifts to a `2`-simplex of `X` with
`2`nd face `w` and `1`st face `id_v` (`SSet.exists_compStruct_of_leftFibration`); its `0`th
face is the required edge `v' → v` over `ū`.
-/

universe u

open CategoryTheory

open scoped Simplicial

namespace SSet

variable {X Y : SSet.{u}}

/-- **Kerodon Tag 01EW** (Example 4.4.1.11): a left fibration is an isofibration. Given an
equivalence `ū : y₀ → y₁` of `Y` with a chosen inverse `J`, and a vertex `v` of `X` over `y₁`,
there is an edge `e : v' → v` of `X` over `ū`. -/
lemma exists_edge_of_leftFibration (q : X ⟶ Y) [LeftFibration q]
    {y₀ y₁ : Y _⦋0⦌} {ū : Y.Edge y₀ y₁} (J : ū.InvStruct) (v : X _⦋0⦌)
    (hv : q.app _ v = y₁) :
    ∃ (v' : X _⦋0⦌) (e : X.Edge v' v), q.app _ e.edge = ū.edge := by
  subst hv
  -- lift the inverse `ū⁻¹ : q(v) → y₀` to an edge `w` with source `v`
  obtain ⟨w, hw₁, hwq, -⟩ := CocartesianFibration.exists_isCocartesianEdge q v J.inv.edge
    (by rw [J.inv.src_eq])
  let e₀₁ : X.Edge v (X.δ 0 w) := Edge.mk w hw₁ rfl
  -- fill the `Λ[2, 0]`-horn `(w, id_v)` over the `2`-simplex witnessing `ū ∘ ū⁻¹ ≃ id`
  obtain ⟨e₁₂, -, he⟩ := exists_compStruct_of_leftFibration q e₀₁ (Edge.id v)
    J.invHomId.simplex (by rw [J.invHomId.d₂]; exact hwq.symm)
    (by rw [J.invHomId.d₁]; simp [SimplicialObject.σ])
  exact ⟨_, e₁₂, by rw [he, J.invHomId.d₀]⟩

/-- **Kerodon Tag 01EW** (Example 4.4.1.11), from `ū.IsEquiv`. -/
lemma exists_edge_of_leftFibration_of_isEquiv (q : X ⟶ Y) [LeftFibration q]
    {y₀ y₁ : Y _⦋0⦌} {ū : Y.Edge y₀ y₁} (hū : ū.IsEquiv) (v : X _⦋0⦌)
    (hv : q.app _ v = y₁) :
    ∃ (v' : X _⦋0⦌) (e : X.Edge v' v), q.app _ e.edge = ū.edge :=
  hū.elim fun J ↦ exists_edge_of_leftFibration q J v hv

end SSet
