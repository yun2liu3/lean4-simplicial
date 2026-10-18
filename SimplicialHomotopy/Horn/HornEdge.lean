/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Outer horns: the initial edge, and the two horns of `Δ[1]`

`SSet.horn.edge₀₁ n : (Λ[n + 2, 0] : SSet) _⦋1⦌` is the edge `0 → 1` of the outer horn
`Λ[n + 2, 0]`. It exists because `#{0, 0, 1} = 2 ≤ n + 2`.

This one definition is the shared hypothesis of the two statements that single out the
initial edge of an outer horn:

* `SSet.FillOuterHornOfIsEquiv` (`Equivalence/KanOfEquiv.lean`), Joyal's special outer horn
  theorem: the horn fills when its initial edge is an equivalence;
* `SSet.IsCocartesianEdge` (`Fibration/Cocartesian.lean`), Kerodon Tag 01T5: the edge `e`
  is `p`-cocartesian when every such horn with initial edge `e` lifts against `p`.

It lives in its own file so that neither of those two files has to import the other.

The file also identifies the two horns of `Δ[1]` with its vertices,
`SSet.horn_one_zero_eq_face : Λ[1, 0] = face {0}` and
`SSet.horn_one_one_eq_face : Λ[1, 1] = face {1}`, which every file that treats a vertex
inclusion `Δ[0] ⟶ Δ[1]` as a horn inclusion needs.
-/

universe u

open CategoryTheory

open scoped Simplicial

namespace SSet.horn

/-- The initial edge `0 → 1` of the outer horn `Λ[n + 2, 0]`. -/
def edge₀₁ (n : ℕ) : (Λ[n + 2, 0] : SSet.{u}) _⦋1⦌ :=
  horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by
    rw [Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)]
    exact Finset.card_le_two.trans (by omega))

end SSet.horn

namespace SSet

/-! ### The horns of `Δ[1]` are its vertices -/

/-- `Λ[1, 0]`, the union of the faces of `Δ[1]` other than the `0`th, is the vertex `{0}` of
`Δ[1]`. -/
lemma horn_one_zero_eq_face : (Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex) = stdSimplex.face {0} := by
  rw [horn_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun j ↦ ?_
    obtain ⟨j, hj⟩ := j
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hj
    fin_cases j
    · exact absurd rfl hj
    · change stdSimplex.face {(1 : Fin 2)}ᶜ ≤ _
      exact le_of_eq (congrArg _ (by decide))
  · exact le_iSup_of_le ⟨1, by simp⟩ (le_of_eq (congrArg _ (by decide)))

/-- `Λ[1, 1]`, the union of the faces of `Δ[1]` other than the `1`st, is the vertex `{1}` of
`Δ[1]`. -/
lemma horn_one_one_eq_face : (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex) = stdSimplex.face {1} := by
  rw [horn_eq_iSup]
  apply le_antisymm
  · refine iSup_le fun j ↦ ?_
    obtain ⟨j, hj⟩ := j
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hj
    fin_cases j
    · change stdSimplex.face {(0 : Fin 2)}ᶜ ≤ _
      exact le_of_eq (congrArg _ (by decide))
    · exact absurd rfl hj
  · exact le_iSup_of_le ⟨0, by simp⟩ (le_of_eq (congrArg _ (by decide)))

end SSet
