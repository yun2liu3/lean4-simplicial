import Simplicial.SSet.Basic

/-!
# Boundary of the Standard Simplex

The boundary `∂Δ[n]` is the simplicial subset of `Δ[n]` consisting of
non-surjective simplices (those that miss at least one vertex of `[n]`).
-/

open CategoryTheory
open Simplicial

namespace SSet

/-- The boundary `∂Δ[n]` of the standard `n`-simplex.
An `m`-simplex of `∂Δ[n]` is a non-surjective monotone map `[m] → [n]`. -/
def boundary (n : ℕ) : SSet.{0} where
  obj m := { α : (m.unop ⟶ ([n] : SimplexCategory)) // ¬Function.Surjective α.toOrderHom }
  map f α := ⟨f.unop ≫ α.1, by
    intro h; apply α.property; intro y
    obtain ⟨x, hx⟩ := h y
    exact ⟨f.unop.toOrderHom x, hx⟩⟩
  map_id m := by funext ⟨α, _⟩; simp [Subtype.ext_iff]
  map_comp f g := by funext ⟨α, _⟩; simp [Subtype.ext_iff]

/-- Notation `∂Δ[n]` for the boundary of the standard `n`-simplex. -/
scoped[Simplicial] notation3 "∂Δ[" n "]" => SSet.boundary n

/-- The inclusion `∂Δ[n] ⟶ Δ[n]`. -/
def boundaryInclusion (n : ℕ) : ∂Δ[n] ⟶ Δ[n] where
  app m α := α.1

end SSet
