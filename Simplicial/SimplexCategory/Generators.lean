import Simplicial.SimplexCategory.Basic

/-!
# Face and Degeneracy Maps

We define the face maps `δ i : [n] ⟶ [n+1]` and degeneracy maps `σ i : [n+1] ⟶ [n]`
in the simplex category.

* `δ i` is the unique injective order-preserving map `[n] → [n+1]` that skips `i`.
  It is defined via `Fin.succAbove`.
* `σ i` is the unique surjective order-preserving map `[n+1] → [n]` that doubles `i`.
  It is defined via `Fin.predAbove`.
-/

open CategoryTheory
open Simplicial

namespace SimplexCategory

/-- The `i`-th face map from `[n]` to `[n+1]`.
  The unique injective order-preserving map that skips `i`. -/
def δ {n : ℕ} (i : Fin (n + 2)) : ([n] : SimplexCategory) ⟶ [n + 1] :=
  Hom.mk (Fin.succAboveOrderEmb i).toOrderHom

/-- The `i`-th degeneracy map from `[n+1]` to `[n]`.
  The unique surjective order-preserving map that doubles `i`. -/
def σ {n : ℕ} (i : Fin (n + 1)) : ([n + 1] : SimplexCategory) ⟶ [n] :=
  Hom.mk ⟨Fin.predAbove i, Fin.predAbove_right_monotone i⟩

@[simp]
theorem δ_toOrderHom {n : ℕ} (i : Fin (n + 2)) :
    (δ i).toOrderHom = (Fin.succAboveOrderEmb i).toOrderHom := rfl

@[simp]
theorem σ_toOrderHom {n : ℕ} (i : Fin (n + 1)) :
    (σ i).toOrderHom = ⟨Fin.predAbove i, Fin.predAbove_right_monotone i⟩ := rfl

end SimplexCategory
