/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.RightFibrations
import SimplicialHomotopy.Horn.OuterHorn
import SimplicialHomotopy.Fibration.Conservative

/-!
# Fibers of a map of simplicial sets over a vertex

For `q : E ⟶ B` and a vertex `b` of `B`, the fiber `SSet.fiber q b` is the pullback of `q`
along `const b : 𝟙_ SSet ⟶ B`. When `q` is a right fibration the fiber is a Kan complex:
it is a quasicategory (right fibration over a point), and every edge of it is an
equivalence because right fibrations are conservative (Kerodon 019K) and every edge of
a point is an equivalence; Kerodon 019D then applies.

## Main declarations

* `SSet.fiber q b`, `SSet.fiberι q b : fiber q b ⟶ E`, `SSet.fiberProj q b : fiber q b ⟶ 𝟙_ SSet`.
* `SSet.kanComplex_of_isTerminal`, `instance : KanComplex (𝟙_ SSet)`.
* `instance [RightFibration q] : RightFibration (fiberProj q b)`,
  `instance [RightFibration q] : Quasicategory (fiber q b)`,
  `instance [RightFibration q] : KanComplex (fiber q b)`.
-/

universe u

open CategoryTheory Limits MonoidalCategory

open scoped Simplicial

namespace SSet

/-- A terminal simplicial set is a Kan complex. -/
lemma kanComplex_of_isTerminal {T : SSet.{u}} (hT : IsTerminal T) : KanComplex T := by
  rw [kanComplex_iff_fillsHorn]
  intro n i
  rw [fillsHorn_iff]
  intro σ₀
  exact ⟨hT.from _, hT.hom_ext _ _⟩

instance : KanComplex (𝟙_ SSet.{u}) :=
  kanComplex_of_isTerminal CartesianMonoidalCategory.isTerminalTensorUnit

instance : KanComplex (⊤_ SSet.{u}) := kanComplex_of_isTerminal terminalIsTerminal

section

variable {E B : SSet.{u}} (q : E ⟶ B) (b : B _⦋0⦌)

/-- The fiber of `q : E ⟶ B` over the vertex `b`. -/
noncomputable abbrev fiber : SSet.{u} := pullback q (const b : 𝟙_ SSet.{u} ⟶ B)

/-- The inclusion of the fiber into the total space. -/
noncomputable abbrev fiberι : fiber q b ⟶ E := pullback.fst q (const b)

/-- The (unique) map from the fiber to the point. -/
noncomputable abbrev fiberProj : fiber q b ⟶ 𝟙_ SSet.{u} := pullback.snd q (const b)

lemma fiberι_comp : fiberι q b ≫ q = fiberProj q b ≫ const b := pullback.condition

lemma fiberι_comp_eq_const : fiberι q b ≫ q = const b := by
  rw [fiberι_comp, comp_const]

instance : Mono (const b : 𝟙_ SSet.{u} ⟶ B) :=
  CartesianMonoidalCategory.isTerminalTensorUnit.mono_from _

instance : Mono (fiberι q b) := pullback.fst_of_mono

/-- The fiber of a right fibration over a point is a right fibration over the point. -/
instance [RightFibration q] : RightFibration (fiberProj q b) :=
  ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback q (const b))
    (mem_rightFibrations q)⟩

/-- The fiber of a right fibration is a quasicategory. -/
instance [RightFibration q] : Quasicategory (fiber q b) :=
  quasicategory_of_innerFibration (fiberProj q b)

/-- The fiber of a right fibration over a vertex is a Kan complex (Kerodon 019D + 019K). -/
instance [RightFibration q] : KanComplex (fiber q b) :=
  kanComplex_of_isEquiv_edges (fiber q b)
    (fun e ↦ SimplicialHomotopy.isEquiv_of_rightFibration (fiberProj q b)
      (KanComplex.isEquiv_edge (e.map (fiberProj q b))))
    fillOuterHornOfIsEquiv

end

end SSet
