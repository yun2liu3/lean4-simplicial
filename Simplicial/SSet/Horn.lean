import Simplicial.SSet.Basic

/-!
# Horns

The horn `Λ[n, i]` is the simplicial subset of `Δ[n]` consisting of
simplices whose image misses at least one vertex of `[n]` other than `i`.
-/

open CategoryTheory
open Simplicial

namespace SSet

/-- The `i`-th horn `Λ[n, i]` of the standard `n`-simplex.
An `m`-simplex of `Λ[n, i]` is a monotone map `[m] → [n]` whose image,
even after adding the vertex `i`, does not cover all of `[n]`. -/
def horn (n : ℕ) (i : Fin (n + 1)) : SSet.{0} where
  obj m := { α : (m.unop ⟶ ([n] : SimplexCategory)) //
    ∃ j : Fin (n + 1), j ≠ i ∧ ∀ k, α.toOrderHom k ≠ j }
  map f α := ⟨f.unop ≫ α.1, by
    obtain ⟨j, hne, hmiss⟩ := α.property
    exact ⟨j, hne, fun k => hmiss (f.unop.toOrderHom k)⟩⟩
  map_id m := by funext ⟨α, _⟩; simp [Subtype.ext_iff]
  map_comp f g := by funext ⟨α, _⟩; simp [Subtype.ext_iff]

/-- Notation `Λ[n, i]` for the `i`-th horn of the standard `n`-simplex. -/
scoped[Simplicial] notation3 "Λ[" n ", " i "]" => SSet.horn (n : ℕ) i

/-- The inclusion `Λ[n, i] ⟶ Δ[n]`. -/
def hornInclusion (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ Δ[n] where
  app m α := α.1

end SSet
