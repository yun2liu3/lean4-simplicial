/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Equivalence.WeakEquivalenceKan

/-!
# Maps out of a weakly contractible simplicial set into a Kan complex are homotopic to a constant

If `X` is weakly contractible (`SSet.WeaklyContractible`) and `K` is a Kan complex, every map
`φ : X ⟶ K` is homotopic to a constant map. This is the `π₀`-part of weak contractibility, and
an invariant that can show that a simplicial set is *not* weakly contractible.

* `SSet.exists_eq_const_of_terminal` : every map `⊤_ SSet ⟶ K` is `const k` for some vertex `k`.
* `SSet.WeaklyContractible.exists_homotopy_const` : `∃ k, Nonempty (Homotopy (const k) φ)`.
* `SSet.WeaklyContractible.exists_homotopy_to_const` : `∃ k, Nonempty (Homotopy φ (const k))`.

The homotopy is the one of `SSet.WeaklyContractible.exists_homotopy_terminal_from_comp`
(`Equivalence/WeakEquivalenceKan.lean`), from `terminal.from X ≫ φ'` to `φ`; the map
`terminal.from X ≫ φ'` is constant.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits CartesianMonoidalCategory

open scoped Simplicial

namespace SSet

variable {X K : SSet.{u}}

/-- The unique vertex of `⊤_ SSet`. -/
noncomputable def terminalVertex : (⊤_ SSet.{u}) _⦋0⦌ :=
  yonedaEquiv (terminal.from Δ[0])

/-- Every map `X ⟶ ⊤_ SSet` is the constant map at the vertex of `⊤_ SSet`. -/
lemma terminal_from_eq_const (X : SSet.{u}) :
    terminal.from X = const terminalVertex :=
  Subsingleton.elim _ _

/-- A map out of the terminal simplicial set is constant. -/
lemma exists_eq_const_of_terminal (ψ : ⊤_ SSet.{u} ⟶ K) :
    ∃ k : K _⦋0⦌, terminal.from X ≫ ψ = const k :=
  ⟨ψ.app _ terminalVertex, by rw [terminal_from_eq_const, const_comp]⟩

/-- Into a Kan complex, every map out of a weakly contractible simplicial set is homotopic
to a constant map (homotopy from the constant map). -/
theorem WeaklyContractible.exists_homotopy_const [KanComplex K] (hX : WeaklyContractible X)
    (φ : X ⟶ K) : ∃ k : K _⦋0⦌, Nonempty (Homotopy (const k) φ) := by
  obtain ⟨φ', ⟨H⟩⟩ := hX.exists_homotopy_terminal_from_comp φ
  obtain ⟨k, hk⟩ := exists_eq_const_of_terminal (X := X) φ'
  exact ⟨k, ⟨H.ofEq' hk rfl⟩⟩

/-- Into a Kan complex, every map out of a weakly contractible simplicial set is homotopic
to a constant map (homotopy to the constant map). -/
theorem WeaklyContractible.exists_homotopy_to_const [KanComplex K] (hX : WeaklyContractible X)
    (φ : X ⟶ K) : ∃ k : K _⦋0⦌, Nonempty (Homotopy φ (const k)) := by
  obtain ⟨k, ⟨H⟩⟩ := hX.exists_homotopy_const φ
  exact ⟨k, H.symm_of_kan⟩

end SSet
