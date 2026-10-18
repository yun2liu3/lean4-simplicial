import Simplicial.SimplicialObject
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types

/-!
# Simplicial Sets

The category of simplicial sets `SSet` is `SimplicialObject (Type u)`.
We define the standard simplex `Δ[n]` via the Yoneda embedding.
-/

open CategoryTheory
open Simplicial

universe u

/-- The category of simplicial sets.
This is the category of contravariant functors from `SimplexCategory` to `Type u`. -/
def SSet : Type (u + 1) :=
  SimplicialObject (Type u)

namespace SSet

instance : Category SSet.{u} :=
  inferInstanceAs (Category (SimplicialObject (Type u)))

/-- The standard simplex `Δ[n]` as a simplicial set.
`Δ[n]` is the Yoneda embedding of `[n]`, mapping `[m] ↦ Hom([m], [n])`. -/
noncomputable def standardSimplex : SimplexCategory ⥤ SSet.{0} :=
  yoneda

/-- Notation `Δ[n]` for the standard `n`-simplex. -/
scoped[Simplicial] notation3 "Δ[" n "]" =>
  SSet.standardSimplex.obj (SimplexCategory.mk n)

/-- The canonical bijection `(Δ[n] ⟶ X) ≃ X _[n]`.
This is the Yoneda lemma applied to simplicial sets. -/
noncomputable def yonedaEquiv (X : SSet.{0}) (n : SimplexCategory) :
    (standardSimplex.obj n ⟶ X) ≃ X.obj (Opposite.op n) :=
  CategoryTheory.yonedaEquiv

end SSet
