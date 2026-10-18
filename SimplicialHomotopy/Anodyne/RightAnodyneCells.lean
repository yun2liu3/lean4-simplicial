/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Anodyne.RightAnodyne
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# The small object argument for right horn inclusions

The right-horn mirror of `SimplicialHomotopy.Anodyne.LeftAnodyneCells`.
`SSet.rightAnodyneExtensions`
is *defined* as `rightFibrations.llp` (see `SimplicialHomotopy.Fibration.RightFibrations`), so a
hypothesis `rightAnodyneExtensions f` cannot be used by induction on cells as it stands. This
file supplies the small object argument for `SSet.rightHornInclusions`.

* `SSet.rightHornInclusions_eq_iSup` : the `iSup`-of-`ofHoms` presentation of the
  inductively defined class of right horn inclusions.
* `MorphismProperty.IsSmall`, `IsCardinalForSmallObjectArgument … Cardinal.aleph0` and
  `HasSmallObjectArgument` instances for `SSet.rightHornInclusions`.
* `SSet.rightAnodyneExtensions_eq_retracts_transfiniteCompositions` and
  `SSet.rightAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape` : right anodyne
  extensions are exactly the retracts of (`ℕ`-indexed) transfinite compositions of pushouts
  of coproducts of right horn inclusions.
* `SSet.rightHornInclusions_le_rightAnodyneExtensions`,
  `SSet.rightAnodyneExtensions_le_iff`, `SSet.rightAnodyneExtensions_le` and
  `SSet.rightAnodyneExtensions_le_of_nat` : the resulting induction principles. The last one
  only asks for stability under `ℕ`-indexed transfinite compositions, which is what the
  base-change closure of `SimplicialHomotopy.Anodyne.BaseChangeClosure` provides.
* `SSet.exists_rightAnodyneExtensions_rightFibration_factorization` : every map factors as
  a right anodyne extension followed by a right fibration (the small object argument).
-/

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty

open scoped Simplicial

namespace SSet

/-- The inductive class `SSet.rightHornInclusions` presented as an indexed supremum of
`MorphismProperty.ofHoms` families, one for each dimension. -/
lemma rightHornInclusions_eq_iSup :
    rightHornInclusions.{u} =
      ⨆ n, .ofHoms (fun p : {p : Fin (n + 2) // 0 < p.1} ↦ Λ[n + 1, p.1].ι) := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain @⟨n, i, hn⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    exact ⟨n, i, hn, rfl⟩
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, hn⟩, _, _⟩ := h
    exact horn_ι_mem_rightHornInclusions hn

attribute [local instance] Cardinal.fact_isRegular_aleph0
  Cardinal.orderBotAleph0OrdToType

instance : MorphismProperty.IsSmall.{u} rightHornInclusions.{u} := by
  rw [rightHornInclusions_eq_iSup]
  have (n : ℕ) : MorphismProperty.IsSmall.{u}
      (MorphismProperty.ofHoms.{u}
        fun p : {p : Fin (n + 2) // 0 < p.1} ↦ Λ[n + 1, p.1].ι) :=
    isSmall_ofHoms ..
  exact isSmall_iSup _

instance : IsCardinalForSmallObjectArgument rightHornInclusions.{u} Cardinal.aleph0.{u} where
  preservesColimit {A B X Y} i hi f hf := by
    have : IsFinitelyPresentable.{u} A := by
      simp only [rightHornInclusions_eq_iSup, iSup_iff] at hi
      obtain ⟨n, ⟨i⟩⟩ := hi
      infer_instance
    infer_instance

instance : HasSmallObjectArgument.{u} rightHornInclusions.{u} where
  exists_cardinal := ⟨.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- The small object argument for right horns: a morphism of simplicial sets is a right
anodyne extension iff it is a retract of a transfinite composition of pushouts of
coproducts of right horn inclusions. -/
theorem rightAnodyneExtensions_eq_retracts_transfiniteCompositions :
    rightAnodyneExtensions.{u} = (transfiniteCompositions.{u}
      (coproducts.{u} rightHornInclusions.{u}).pushouts).retracts := by
  rw [rightAnodyneExtensions_eq_llp_rlp, llp_rlp_of_hasSmallObjectArgument]

/-- The `ℕ`-indexed refinement of `rightAnodyneExtensions_eq_retracts_transfiniteCompositions`. -/
theorem rightAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape :
    rightAnodyneExtensions.{u} = (transfiniteCompositionsOfShape
      (coproducts.{u} rightHornInclusions.{u}).pushouts ℕ).retracts := by
  rw [rightAnodyneExtensions_eq_llp_rlp,
    SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]

/-- Right horn inclusions are right anodyne extensions. -/
lemma rightHornInclusions_le_rightAnodyneExtensions :
    rightHornInclusions.{u} ≤ rightAnodyneExtensions :=
  fun _ _ _ h ↦ le_llp_rlp _ _ h

/-- The induction principle for right anodyne extensions: a class of morphisms that is
stable under cobase change, retracts, coproducts and transfinite composition contains all
right anodyne extensions as soon as it contains the right horn inclusions. -/
theorem rightAnodyneExtensions_le_iff {P : MorphismProperty SSet.{u}}
    [P.IsStableUnderCobaseChange] [P.IsStableUnderRetracts]
    [IsStableUnderCoproducts.{u} P] [IsStableUnderTransfiniteComposition.{u} P] :
    rightAnodyneExtensions.{u} ≤ P ↔ rightHornInclusions.{u} ≤ P := by
  refine ⟨rightHornInclusions_le_rightAnodyneExtensions.trans, fun h ↦ ?_⟩
  rw [rightAnodyneExtensions_eq_retracts_transfiniteCompositions]
  simpa using h

/-- `rightAnodyneExtensions_le_iff` in the direction used for cell induction. -/
theorem rightAnodyneExtensions_le {P : MorphismProperty SSet.{u}}
    [P.IsStableUnderCobaseChange] [P.IsStableUnderRetracts]
    [IsStableUnderCoproducts.{u} P] [IsStableUnderTransfiniteComposition.{u} P]
    (h : rightHornInclusions.{u} ≤ P) : rightAnodyneExtensions.{u} ≤ P :=
  rightAnodyneExtensions_le_iff.2 h

/-- The induction principle for right anodyne extensions asking only for stability under
`ℕ`-indexed transfinite compositions (rather than all of them), which is what the small
object argument at `Cardinal.aleph0` actually produces. -/
theorem rightAnodyneExtensions_le_of_nat {P : MorphismProperty SSet.{u}}
    [P.IsStableUnderCobaseChange] [P.IsStableUnderRetracts]
    [IsStableUnderCoproducts.{u} P] [P.IsStableUnderTransfiniteCompositionOfShape ℕ]
    (h : rightHornInclusions.{u} ≤ P) : rightAnodyneExtensions.{u} ≤ P := by
  rw [rightAnodyneExtensions_eq_retracts_transfiniteCompositionsOfShape]
  refine (retracts_monotone ?_).trans P.retracts_le
  refine (transfiniteCompositionsOfShape_monotone ℕ ?_).trans
    (P.transfiniteCompositionsOfShape_le ℕ)
  refine (pushouts_monotone ?_).trans P.pushouts_le
  exact (coproducts_monotone h).trans P.coproducts_le

/-- The factorization half of the small object argument: every morphism of simplicial
sets factors as a right anodyne extension followed by a right fibration. -/
lemma exists_rightAnodyneExtensions_rightFibration_factorization {X Y : SSet.{u}}
    (f : X ⟶ Y) :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (p : Z ⟶ Y), i ≫ p = f ∧
      rightAnodyneExtensions i ∧ RightFibration p := by
  have : HasFunctorialFactorization rightAnodyneExtensions.{u} rightFibrations.{u} :=
    inferInstanceAs (HasFunctorialFactorization rightHornInclusions.rlp.llp
      rightHornInclusions.rlp)
  obtain ⟨Z, i, p, fac, hi, hp⟩ := factorizationData rightAnodyneExtensions rightFibrations f
  exact ⟨Z, i, p, fac, hi, ⟨hp⟩⟩

end SSet
