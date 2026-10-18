/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Cofinal.Smooth
import SimplicialHomotopy.Slice.UnderHomotopy
import SimplicialHomotopy.Anodyne.RightAnodyneCells
import SimplicialHomotopy.Equivalence.WeakEquivalenceKan
import SimplicialHomotopy.Join.ConeLifting
import SimplicialHomotopy.Cofinal.CofinalBasic
import SimplicialHomotopy.Fibration.TrivialFibration
import SimplicialHomotopy.Cofinal.CofinalConverse

/-!
# Joyal's Theorem A: the assembly

This file assembles [Lur09, Theorem 4.1.3.1] (Joyal's version of Quillen's Theorem A) from
the pieces proved in this library:

1. factor `p : S ⟶ C` as a right anodyne extension `i : S ⟶ Z` followed by a right fibration
   `q : Z ⟶ C` (`RightAnodyneCells.lean`);
2. for a vertex `c`, the comparison map `S ×_C C_{c/} ⟶ Z ×_C C_{c/}` is the base change of
   `i` along the left fibration `Z ×_C C_{c/} ⟶ Z`, hence right anodyne (`Smooth.lean`), hence
   a weak homotopy equivalence (`WeakEquivalenceKan.lean`); so the hypothesis on `p` transfers
   to `q` (`weaklyContractible_pullback_underProj_of_rightAnodyneExtensions`);
3. for the right fibration `q`, `Z ×_C C_{c/}` deformation retracts onto the fibre `q⁻¹ (c)`
   (`UnderHomotopy.lean`), so all fibres of `q` are weakly contractible
   (`weaklyContractible_fiber_of_rightAnodyneExtensions`);
4. a right fibration with weakly contractible fibres has the right lifting property against
   monomorphisms (`TrivialFibration.lean`), such a map is cofinal, right anodyne maps are
   cofinal and the composite is cofinal (`CofinalBasic.lean`).

Both directions are proved in this file: `SSet.isCofinal_of_weaklyContractible_pullback_underProj`
(steps 1–4) and the converse `SSet.weaklyContractible_pullback_underProj_of_isCofinal`, which
uses the same factorization and the two facts of `CofinalConverse.lean`. They are re-exported as
`SSet.HTT.isCofinal_of_weaklyContractible` and `SSet.HTT.weaklyContractible_of_isCofinal`.
-/

universe u

open CategoryTheory Limits
open scoped Simplicial

namespace SSet

/-- The comparison map `S ×_C C_{c/} ⟶ Z ×_C C_{c/}` induced by `i : S ⟶ Z` over `C`. -/
noncomputable def pullbackUnderMap {S Z C : SSet.{u}} (i : S ⟶ Z) (q : Z ⟶ C) (c : C _⦋0⦌) :
    pullback (i ≫ q) (C.underProj c) ⟶ pullback q (C.underProj c) :=
  pullback.lift (pullback.fst _ _ ≫ i) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma pullbackUnderMap_fst {S Z C : SSet.{u}} (i : S ⟶ Z) (q : Z ⟶ C) (c : C _⦋0⦌) :
    pullbackUnderMap i q c ≫ pullback.fst q (C.underProj c) =
      pullback.fst (i ≫ q) (C.underProj c) ≫ i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackUnderMap_snd {S Z C : SSet.{u}} (i : S ⟶ Z) (q : Z ⟶ C) (c : C _⦋0⦌) :
    pullbackUnderMap i q c ≫ pullback.snd q (C.underProj c) =
      pullback.snd (i ≫ q) (C.underProj c) :=
  pullback.lift_snd _ _ _

/-- `pullbackUnderMap i q c` is the base change of `i` along `Z ×_C C_{c/} ⟶ Z`
(pasting of pullbacks). -/
lemma isPullback_pullbackUnderMap {S Z C : SSet.{u}} (i : S ⟶ Z) (q : Z ⟶ C) (c : C _⦋0⦌) :
    IsPullback (pullback.fst (i ≫ q) (C.underProj c)) (pullbackUnderMap i q c) i
      (pullback.fst q (C.underProj c)) := by
  refine (IsPullback.of_right ?_ (pullbackUnderMap_fst i q c)
    (IsPullback.of_hasPullback q (C.underProj c)).flip).flip
  rw [pullbackUnderMap_snd]
  exact (IsPullback.of_hasPullback _ _).flip

/-- Step 2 of Theorem A (smoothness): if `i` is right anodyne, so is the comparison map
`S ×_C C_{c/} ⟶ Z ×_C C_{c/}`, because `Z ×_C C_{c/} ⟶ Z` is a left fibration. -/
theorem rightAnodyneExtensions_pullbackUnderMap {S Z C : SSet.{u}} [Quasicategory C]
    {i : S ⟶ Z} (hi : rightAnodyneExtensions i) (q : Z ⟶ C) (c : C _⦋0⦌) :
    rightAnodyneExtensions (pullbackUnderMap i q c) := by
  have hu : LeftFibration (C.underProj c) :=
    leftFibration_underProj_of_innerAnodyne_cone innerAnodyneConeOfLeftAnodyne C c
  have hfst : LeftFibration (pullback.fst q (C.underProj c)) :=
    ⟨leftFibrations.pullback_fst q _ (mem_leftFibrations _)⟩
  exact rightAnodyneExtensions_of_isPullback_of_leftFibration hi (isPullback_pullbackUnderMap i q c)

/-- If `i` is right anodyne, the comparison map `S ×_C C_{c/} ⟶ Z ×_C C_{c/}` is a weak homotopy
equivalence. -/
theorem isWeakHomotopyEquivalence_pullbackUnderMap {S Z C : SSet.{u}} [Quasicategory C]
    {i : S ⟶ Z} (hi : rightAnodyneExtensions i) (q : Z ⟶ C) (c : C _⦋0⦌) :
    IsWeakHomotopyEquivalence (pullbackUnderMap i q c) :=
  IsWeakHomotopyEquivalence.of_anodyneExtensions
    (rightAnodyneExtensions_le_anodyneExtensions _ (rightAnodyneExtensions_pullbackUnderMap hi q c))

/-- Step 2 of Theorem A: if `p = i ≫ q` with `i` right anodyne, weak contractibility of
`S ×_C C_{c/}` transfers to `Z ×_C C_{c/}`. -/
theorem weaklyContractible_pullback_underProj_of_rightAnodyneExtensions
    {S Z C : SSet.{u}} [Quasicategory C] {i : S ⟶ Z} (hi : rightAnodyneExtensions i)
    (q : Z ⟶ C) (c : C _⦋0⦌) (h : WeaklyContractible (pullback (i ≫ q) (C.underProj c))) :
    WeaklyContractible (pullback q (C.underProj c)) :=
  weaklyContractible_tgt_of_isWeakHomotopyEquivalence
    (isWeakHomotopyEquivalence_pullbackUnderMap hi q c) h

/-- Step 3 of Theorem A: for `p = i ≫ q` with `i` right anodyne and `q` a right fibration,
the fibres of `q` are weakly contractible. -/
theorem weaklyContractible_fiber_of_rightAnodyneExtensions
    {S Z C : SSet.{u}} [Quasicategory C] {i : S ⟶ Z} (hi : rightAnodyneExtensions i)
    (q : Z ⟶ C) [RightFibration q] (c : C _⦋0⦌)
    (h : WeaklyContractible (pullback (i ≫ q) (C.underProj c))) :
    WeaklyContractible (fiber q c) :=
  weaklyContractible_fiber_of_pullback_under q c
    (weaklyContractible_pullback_underProj_of_rightAnodyneExtensions hi q c h)

/-! ### Theorem A, forward direction -/

/-- **Joyal's Theorem A**, [Lur09, Theorem 4.1.3.1], forward direction: if every
`S ×_C C_{c/}` is weakly contractible then `p` is cofinal. Factor `p = i ≫ q` with `i` right
anodyne and `q` a right fibration; the hypothesis transfers to the fibres of `q`, so `q` is a
trivial fibration, hence cofinal; and `i` is right anodyne, hence cofinal. -/
theorem isCofinal_of_weaklyContractible_pullback_underProj {S C : SSet.{u}} [Quasicategory C]
    (p : S ⟶ C) (h : ∀ c : C _⦋0⦌, WeaklyContractible (pullback p (C.underProj c))) :
    IsCofinal p := by
  obtain ⟨Z, i, q, rfl, hi, hq⟩ := exists_rightAnodyneExtensions_rightFibration_factorization p
  exact isCofinal_comp_of_rightAnodyneExtensions hi (isCofinal_of_rlp_monomorphisms q
    (rlp_monomorphisms_of_rightFibration_of_weaklyContractible_fibers q
      fun c ↦ weaklyContractible_fiber_of_rightAnodyneExtensions hi q c (h c)))

/-! ### Theorem A, converse direction -/

/-- [Lur09, Theorem 4.1.3.1], converse direction: if `p` is cofinal then every `S ×_C C_{c/}`
is weakly contractible. Factor `p = i ≫ q` as above; cofinality descends to `q`, whose fibres
are then weakly contractible; transfer to `Z ×_C C_{c/}` along the fibre inclusion and back to
`S ×_C C_{c/}` along the right anodyne comparison map. -/
theorem weaklyContractible_pullback_underProj_of_isCofinal {S C : SSet.{u}} [Quasicategory C]
    (p : S ⟶ C) (hp : IsCofinal p) (c : C _⦋0⦌) :
    WeaklyContractible (pullback p (C.underProj c)) := by
  obtain ⟨Z, i, q, rfl, hi, hq⟩ := exists_rightAnodyneExtensions_rightFibration_factorization p
  exact weaklyContractible_of_isWeakHomotopyEquivalence (pullbackUnderMap i q c)
    (isWeakHomotopyEquivalence_pullbackUnderMap hi q c)
    (weaklyContractible_tgt_of_isWeakHomotopyEquivalence
      (isHomotopyEquivalence_fiberToPullbackUnder q c).isWeakHomotopyEquivalence
      (weaklyContractible_fiber_of_isCofinal q
        (isCofinal_of_comp_of_rightAnodyneExtensions hi q hp) c))

end SSet
