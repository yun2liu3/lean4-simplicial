import Simplicial.SimplexCategory.Identities
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites

/-!
# Simplicial Objects

A simplicial object in a category `C` is a functor `SimplexCategoryᵒᵖ ⥤ C`.

We define face and degeneracy maps on simplicial objects and show the
simplicial identities hold automatically by functoriality.
-/

open CategoryTheory
open Simplicial

universe v u

/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `SimplexCategory` to `C`. -/
def SimplicialObject (C : Type u) [Category.{v} C] :=
  SimplexCategoryᵒᵖ ⥤ C

namespace SimplicialObject

variable {C : Type u} [Category.{v} C]

instance : Category (SimplicialObject C) :=
  inferInstanceAs (Category (SimplexCategoryᵒᵖ ⥤ C))

/-- Notation `X _[n]` for the `n`-th component of a simplicial object. -/
scoped[Simplicial] notation3:1000 X " _[" n "]" =>
  (X : SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

variable (X : SimplicialObject C)

/-- Face maps for a simplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.δ i).op

/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.σ i).op

/-- Face-face identity: for `i ≤ j`,
  `X.δ j.succ ≫ X.δ i = X.δ (castSucc i) ≫ X.δ j`. -/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ (Fin.castSucc i) ≫ X.δ j := by
  simp only [δ, ← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]

/-- Face-degeneracy identity: `X.σ i ≫ X.δ (castSucc i) = 𝟙`. -/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    X.σ i ≫ X.δ (Fin.castSucc i) = 𝟙 _ := by
  simp only [δ, σ, ← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]

/-- Face-degeneracy identity: `X.σ i ≫ X.δ i.succ = 𝟙`. -/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} :
    X.σ i ≫ X.δ i.succ = 𝟙 _ := by
  simp only [δ, σ, ← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]

/-- Face-degeneracy identity: for `i ≤ castSucc j`,
  `X.σ j.succ ≫ X.δ (castSucc i) = X.δ i ≫ X.σ j`. -/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (H : i ≤ Fin.castSucc j) :
    X.σ j.succ ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.σ j := by
  simp only [δ, σ, ← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- Degeneracy-degeneracy identity: for `i ≤ j`,
  `X.σ j ≫ X.σ (castSucc i) = X.σ i ≫ X.σ j.succ`. -/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ j ≫ X.σ (Fin.castSucc i) = X.σ i ≫ X.σ j.succ := by
  simp only [σ, ← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]

end SimplicialObject
