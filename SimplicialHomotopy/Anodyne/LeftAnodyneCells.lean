/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Anodyne.LeftAnodyne
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# The small object argument for left horn inclusions

`SSet.leftAnodyneExtensions` is *defined* as a left lifting property class
(`leftFibrations.llp`, see `SimplicialHomotopy.Fibration.LeftFibrations`), so a hypothesis
`leftAnodyneExtensions f` cannot be used by induction on cells as it stands. This file
supplies the missing small object argument, mirroring verbatim what Mathlib does for all
horns in `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic` and for inner
horns in `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic`.

* `SSet.leftHornInclusions_eq_iSup` : the `iSup`-of-`ofHoms` presentation of the
  (inductively defined) class of left horn inclusions. The inductive definition stays the
  public face; this presentation is only what the smallness instances need.
* `MorphismProperty.IsSmall`, `IsCardinalForSmallObjectArgument … Cardinal.aleph0` and
  `HasSmallObjectArgument` instances for `SSet.leftHornInclusions`.
* `SSet.leftAnodyneExtensions_eq_retracts_transfiniteCompositions` and
  `SSet.leftAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape` : left anodyne
  extensions are exactly the retracts of transfinite compositions of pushouts of
  coproducts of left horn inclusions (the small object argument; compare [Lur09, §2.1.2]).
* `SSet.leftHornInclusions_le_leftAnodyneExtensions`,
  `SSet.leftAnodyneExtensions_le_iff` and `SSet.leftAnodyneExtensions_le` : the resulting
  induction principle. For `P : MorphismProperty SSet` stable under cobase change,
  retracts, coproducts and transfinite composition, `leftHornInclusions ≤ P` implies
  `leftAnodyneExtensions ≤ P`.
-/

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty

open scoped Simplicial

namespace SSet

/-- The inductive class `SSet.leftHornInclusions` presented as an indexed supremum of
`MorphismProperty.ofHoms` families, one for each dimension. This is the shape the
smallness instances below need; downstream files should keep using the inductive
constructor. -/
lemma leftHornInclusions_eq_iSup :
    leftHornInclusions.{u} =
      ⨆ n, .ofHoms (fun p : {p : Fin (n + 2) // p < Fin.last (n + 1)} ↦ Λ[n + 1, p.1].ι) := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain @⟨n, i, hn⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    use n, i
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, hn⟩, _, _⟩ := h
    exact horn_ι_mem_leftHornInclusions hn

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance : MorphismProperty.IsSmall.{u} leftHornInclusions.{u} := by
  rw [leftHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
      (MorphismProperty.ofHoms.{u}
        fun p : {p : Fin (n + 2) // p < Fin.last (n + 1)} ↦ Λ[n + 1, p.1].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

instance : IsCardinalForSmallObjectArgument leftHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [leftHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} leftHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- The small object argument for left horns: a morphism of simplicial sets is a left
anodyne extension iff it is a retract of a transfinite composition of pushouts of
coproducts of left horn inclusions. This is the cell description asserted by the
docstring of `SSet.leftAnodyneExtensions`. -/
theorem leftAnodyneExtensions_eq_retracts_transfiniteCompositions :
    leftAnodyneExtensions.{u} = (transfiniteCompositions.{u}
      (coproducts.{u} leftHornInclusions.{u}).pushouts).retracts := by
  rw [leftAnodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument]

/-- The `ℕ`-indexed refinement of `leftAnodyneExtensions_eq_retracts_transfiniteCompositions`:
since `leftHornInclusions` has `Cardinal.aleph0` as a cardinal for the small object
argument, the transfinite compositions may be taken of shape `ℕ`. -/
theorem leftAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    leftAnodyneExtensions.{u} = (transfiniteCompositionsOfShape
      (coproducts.{u} leftHornInclusions.{u}).pushouts ℕ).retracts := by
  rw [leftAnodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

/-- Left horn inclusions are left anodyne extensions. -/
lemma leftHornInclusions_le_leftAnodyneExtensions :
    leftHornInclusions.{u} ≤ leftAnodyneExtensions :=
  fun _ _ _ h ↦ le_llp_rlp _ _ h

/-- The induction principle for left anodyne extensions: a class of morphisms that is
stable under cobase change, retracts, coproducts and transfinite composition contains all
left anodyne extensions as soon as it contains the left horn inclusions. -/
theorem leftAnodyneExtensions_le_iff {P : MorphismProperty SSet.{u}}
    [P.IsStableUnderCobaseChange] [P.IsStableUnderRetracts]
    [IsStableUnderCoproducts.{u} P] [IsStableUnderTransfiniteComposition.{u} P] :
    leftAnodyneExtensions.{u} ≤ P ↔ leftHornInclusions.{u} ≤ P := by
  refine ⟨leftHornInclusions_le_leftAnodyneExtensions.trans, fun h ↦ ?_⟩
  rw [leftAnodyneExtensions_eq_retracts_transfiniteCompositions]
  simpa using h

/-- `leftAnodyneExtensions_le_iff` in the direction used for cell induction. -/
theorem leftAnodyneExtensions_le {P : MorphismProperty SSet.{u}}
    [P.IsStableUnderCobaseChange] [P.IsStableUnderRetracts]
    [IsStableUnderCoproducts.{u} P] [IsStableUnderTransfiniteComposition.{u} P]
    (h : leftHornInclusions.{u} ≤ P) : leftAnodyneExtensions.{u} ≤ P :=
  leftAnodyneExtensions_le_iff.2 h

end SSet
