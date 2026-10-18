/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Join.Cone

/-!
# Relatively initial vertices

For `p : X ⟶ Y` and a vertex `y` of `X`, the vertex `y` is **`p`-initial**
([Lur09, Definition 4.3.1.1] for the one-vertex diagram) if every lifting
problem against `p` for a boundary inclusion `∂Δ[n + 1] ↪ Δ[n + 1]` whose vertex `0` goes to
`y` has a solution. We state the lifting problems in *cone form*: under
`Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]` the boundary `∂Δ[n + 1]` is `(Δ[0] ⋆ ∂Δ[n]) ∪ Δ[n]`, and the vertex `0`
is the cone point. The cone form makes sense for any subcomplex `B₀ ⊆ B`.

* `SSet.coneUnion B₀` : the subcomplex `(Δ[0] ⋆ B₀) ∪ B` of `Δ[0] ⋆ B`.
* `SSet.conePtUnion B₀` : the cone point, as a vertex of `coneUnion B₀`.
* `SSet.HasConeLiftAt p y B₀` : every lifting problem for `coneUnion B₀ ↪ Δ[0] ⋆ B` against `p`
  sending the cone point to `y` has a solution.
* `SSet.IsRelInitial p y` : `HasConeLiftAt p y ∂Δ[n]` for every `n`.

These are only the definitions shared by `RelInitial/RelInitialLift.lean` (cocartesian edges
give relatively initial vertices, and relative initiality gives `HasConeLiftAt` for every
`B₀ ⊆ B`) and `RelInitial/PrismCone.lean` (the prism `Δ[1] ⊗ Δ[n]` as a cone).
-/

universe u

open CategoryTheory Simplicial

namespace SSet

variable {X Y B : SSet.{u}}

/-- The subcomplex `(Δ[0] ⋆ B₀) ∪ B` of `Δ[0] ⋆ B`. -/
abbrev coneUnion (B₀ : B.Subcomplex) : (cone B).Subcomplex :=
  Subcomplex.cone B₀ ⊔ Subcomplex.range (coneι B)

lemma range_conePt_le_coneUnion (B₀ : B.Subcomplex) :
    Subcomplex.range (conePt B) ≤ coneUnion B₀ := by
  rintro n _ ⟨_, rfl⟩
  exact Or.inl (Subcomplex.pt_mem_cone B₀ n)

/-- The cone point of `Δ[0] ⋆ B`, as a vertex of `coneUnion B₀`. -/
def conePtUnion (B₀ : B.Subcomplex) : Δ[0] ⟶ (coneUnion B₀ : SSet.{u}) :=
  Subcomplex.lift (conePt B) (range_conePt_le_coneUnion B₀)

@[simp]
lemma conePtUnion_ι (B₀ : B.Subcomplex) : conePtUnion B₀ ≫ (coneUnion B₀).ι = conePt B := rfl

/-- Every lifting problem for `(Δ[0] ⋆ B₀) ∪ B ↪ Δ[0] ⋆ B` against `p` which sends the cone
point to `y` has a solution. -/
def HasConeLiftAt (p : X ⟶ Y) (y : X _⦋0⦌) (B₀ : B.Subcomplex) : Prop :=
  ∀ (a : (coneUnion B₀ : SSet.{u}) ⟶ X) (b : cone B ⟶ Y), a ≫ p = (coneUnion B₀).ι ≫ b →
    conePtUnion B₀ ≫ a = const y →
      ∃ l : cone B ⟶ X, (coneUnion B₀).ι ≫ l = a ∧ l ≫ p = b

/-- `y` is `p`-initial: `HasConeLiftAt p y ∂Δ[n]` for every `n`, i.e. every lifting problem for
`∂Δ[n + 1] ↪ Δ[n + 1]` against `p` with vertex `0` sent to `y` has a solution. -/
def IsRelInitial (p : X ⟶ Y) (y : X _⦋0⦌) : Prop :=
  ∀ n : ℕ, HasConeLiftAt p y (boundary.{u} n)

end SSet
