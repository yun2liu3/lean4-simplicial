import Simplicial.SSet.Horn

/-!
# Kan Complexes and Quasicategories

A Kan complex is a simplicial set where every horn has a filler.
A quasicategory is a simplicial set where every *inner* horn has a filler.
-/

open CategoryTheory
open Simplicial

namespace SSet

/-- A simplicial set `S` is a *Kan complex* if every horn `Λ[n, i] → S`
can be extended to a map `Δ[n] → S`. -/
class KanComplex (S : SSet.{0}) : Prop where
  hornFilling : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 1)⦄ (σ₀ : Λ[n, i] ⟶ S),
    ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ

/-- A simplicial set `S` is a *quasicategory* if every inner horn
`Λ[n, i] → S` (with `0 < i < n`) can be extended to `Δ[n] → S`. -/
class Quasicategory (S : SSet.{0}) : Prop where
  innerHornFilling : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : Λ[n + 2, i] ⟶ S),
    0 < i → i < Fin.last (n + 2) →
    ∃ σ : Δ[n + 2] ⟶ S, σ₀ = hornInclusion (n + 2) i ≫ σ

/-- Every Kan complex is a quasicategory. -/
instance (S : SSet.{0}) [KanComplex S] : Quasicategory S where
  innerHornFilling := fun {_n} {_i} σ₀ _h0 _hn => KanComplex.hornFilling σ₀

end SSet
