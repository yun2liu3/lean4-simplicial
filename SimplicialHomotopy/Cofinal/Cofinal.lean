/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.RightFibrations
import SimplicialHomotopy.Equivalence.WeakEquivalence
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Cofinal maps of simplicial sets ([Lur09, 4.1.1.1])

A map `p : A ⟶ B` is *cofinal* if for every **right** fibration `q : X ⟶ B`, restriction
along `p` induces a homotopy equivalence of Kan complexes
`Map_B(B, X) ⟶ Map_B(A, X)`. Here `Map_B(A, X)` is the fiber of
`Fun(A, X) ⟶ Fun(A, B)` over the point `f : A ⟶ B` (a Kan complex when `q` is a right
fibration, [Lur09, 2.1.3.1]; we do not need this to *state* cofinality).

The test class is *right* fibrations, as in [Lur09, Definition 4.1.1.1]:

> Let `p : S → T` be a map of simplicial sets. We shall say that `p` is *cofinal* if, for
> any right fibration `X → T`, the induced map `Map_T(T, X) → Map_T(S, X)` is a homotopy
> equivalence.

In Kerodon's terminology this is **right cofinal** (Definition 7.2.1.1, tag 02N1: right
cofinal is tested against right fibrations, left cofinal against left fibrations), and it
is the notion paired with the *under*-categories `B_{b/}` in Joyal's Theorem A
(Theorem 7.2.3.1(2), tag 02NY), which is the form used throughout this library.
Testing against *left* fibrations would define Kerodon's left cofinal instead, which is
paired with the slices `B_{/b}` and is a genuinely different (initial-like) condition.

Joyal's Theorem A
([Lur09, 4.1.3.1]) is proved in `TheoremA.lean` and re-exported in `HTT.lean`
(`SSet.HTT.isCofinal_of_weaklyContractible`, `SSet.HTT.weaklyContractible_of_isCofinal`).
The equivalence with colimit-preservation ([Lur09, 4.1.1.8]) is not stated in this library.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits

namespace SSet

variable {A B X : SSet.{u}}

/-- The point of `Fun(A, B)` classifying `f : A ⟶ B`. -/
def pointOf (f : A ⟶ B) : 𝟙_ SSet.{u} ⟶ (ihom A).obj B :=
  curry ((ρ_ A).hom ≫ f)

/-- The relative mapping space `Map_B(A, X)`: the fiber of
`(ihom A).map q : Fun(A, X) ⟶ Fun(A, B)` over the point `f`. -/
noncomputable def relMap (f : A ⟶ B) (q : X ⟶ B) : SSet.{u} :=
  pullback ((ihom A).map q) (pointOf f)

/-- Naturality of `pointOf` in the source. -/
lemma pointOf_comp_pre {A' : SSet.{u}} (p : A' ⟶ A) (f : A ⟶ B) :
    pointOf f ≫ (pre p).app B = pointOf (p ≫ f) := by
  simp only [pointOf, curry_pre_app, ← Category.assoc, MonoidalCategory.rightUnitor_naturality]

/-- Restriction along `p : A' ⟶ A` on relative mapping spaces,
`Map_B(A, X) ⟶ Map_B(A', X)`. -/
noncomputable def relMapRestrict {A' : SSet.{u}} (p : A' ⟶ A) (f : A ⟶ B) (q : X ⟶ B) :
    relMap f q ⟶ relMap (p ≫ f) q :=
  pullback.map ((ihom A).map q) (pointOf f) ((ihom A').map q) (pointOf (p ≫ f))
    ((pre p).app X) (𝟙 _) ((pre p).app B)
    ((pre p).naturality q) (by rw [pointOf_comp_pre, Category.id_comp])

/-- `p : A ⟶ B` is cofinal ([Lur09, Definition 4.1.1.1]; Kerodon's *right* cofinal,
Definition 7.2.1.1, tag 02N1): for every **right** fibration `q : X ⟶ B`, restriction
`Map_B(B, X) ⟶ Map_B(A, X)` is a homotopy equivalence. -/
def IsCofinal (p : A ⟶ B) : Prop :=
  ∀ (X : SSet.{u}) (q : X ⟶ B) [RightFibration q],
    IsHomotopyEquivalence (relMapRestrict p (𝟙 B) q)

end SSet
