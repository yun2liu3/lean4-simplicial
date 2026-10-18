/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Anodyne.CellLifting
import SimplicialHomotopy.Horn.OuterHorn
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RelativeCellComplex
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat

/-!
# The product cell lemma for the outer horn `Λ[n+2, 0]`

**Kerodon Tag 01DP**, in the special case needed for the pointwise detection of natural
equivalences (Kerodon 01DK, `Equivalence/PointwiseEquiv.lean`): a morphism

  `H₀ : Λ[n+2, 0] × Δ[m] ∪ Δ[n+2] × ∂Δ[m] ⟶ C`

into a quasicategory `C` extends to `Δ[n+2] × Δ[m]` as soon as the edges `(0 → 1) × {t}`
(`SSet.prodStdSimplex.unionProdEdge₀₁ n m t`, for `t : Fin (m+1)`) are sent to equivalences.

## Proof

Mathlib (`Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/UnionProd.lean`) exhibits
the inclusion `Λ[n+2, 0] × Δ[m] ∪ Δ[n+2] × ∂Δ[m] ⊆ Δ[n+2] × Δ[m]` as a relative cell complex
whose cells are horn inclusions `Λ[d+1, i] ⊆ Δ[d+1]` (`SSet.prodStdSimplex.pairingCore 0 m` and
its rank function, `SSet.Subcomplex.Pairing.RankFunction.relativeCellComplex`). The pairing is
regular but not inner: a cell with index `i = 0` occurs exactly when the type (I) simplex starts
with the step `(0, t) → (1, t)`, so its horn `Λ[d+1, 0]` has initial edge `(0 → 1) × {t}`
(`SSet.prodStdSimplex.simplex_map_edge_of_index_eq_zero`); all other cells have
`0 < i < d + 1`. Hence every cell can be filled: inner horns by the quasicategory axiom,
index-`0` horns by Joyal's special outer horn theorem (Kerodon 019F,
`SSet.fillOuterHornOfIsEquiv`), and the `Λ[1, 0]` vertex case by a degenerate edge
(`SSet.fill_horn_of_ne_last`). The extension is then given by the cellwise lifting principle
`SSet.Subcomplex.Pairing.RankFunction.exists_lift` (`Anodyne/CellLifting.lean`), with
target the terminal object.

## Main declarations

* `SSet.fill_horn_of_ne_last` : filling `Λ[d+1, i] ⟶ C`, `i ≠ d + 1`, in a quasicategory when
  the initial edge is an equivalence if `i = 0`.
* `SSet.prodStdSimplex.cell_index_ne_last`, `SSet.prodStdSimplex.cell_map_app_edge` : no cell
  is a last horn, and a cell of index `0` has initial edge `(0 → 1) × {t}`. They use the
  description of the cells of a `PairingCore` in `Anodyne/CellLifting.lean`.
* `SSet.prodStdSimplex.exists_extension_unionProd` : **the product cell lemma**.
-/

universe u

open CategoryTheory Simplicial SimplexCategory Limits Opposite MonoidalCategory

namespace SSet

/-- A horn `Λ[d+1, i] ⟶ C`, `i ≠ d + 1`, into a quasicategory has a filler, provided that its
initial edge `0 → 1` is an equivalence when `i = 0` (Kerodon 019F); `Λ[1, 0]` is a vertex. -/
lemma fill_horn_of_ne_last {C : SSet.{u}} [Quasicategory C] {d : ℕ} (i : Fin (d + 2))
    (hi : i ≠ Fin.last _) (σ₀ : (Λ[d + 1, i] : SSet.{u}) ⟶ C)
    (h0 : ∀ (e : (Λ[d + 1, i] : SSet.{u}) _⦋1⦌), i = 0 →
      e.1 = stdSimplex.edge (d + 1) 0 1 (by simp) → (Edge.mk' (σ₀.app _ e)).IsEquiv) :
    ∃ σ : Δ[d + 1] ⟶ C, σ₀ = Λ[d + 1, i].ι ≫ σ := by
  obtain _ | d := d
  · -- `Λ[1, i]` is a vertex: extend by a degenerate edge
    obtain rfl : i = 0 := by
      fin_cases i
      · rfl
      · exact (hi rfl).elim
    refine ⟨stdSimplex.σ 0 ≫ horn.ι 0 1 (by decide) ≫ σ₀, ?_⟩
    refine horn.hom_ext' fun j hj ↦ ?_
    obtain rfl : j = 1 := by fin_cases j <;> simp_all
    rw [horn.ι_ι_assoc, ← Category.assoc,
      stdSimplex.isTerminalObj₀.hom_ext (stdSimplex.δ 1 ≫ stdSimplex.σ 0) (𝟙 _),
      Category.id_comp]
  · by_cases h : i = 0
    · subst h
      exact fillOuterHornOfIsEquiv σ₀ (h0 _ rfl rfl)
    · exact Quasicategory.hornFilling' σ₀ (Fin.pos_iff_ne_zero.mpr h)
        (Fin.lt_last_iff_ne_last.mpr hi)

namespace prodStdSimplex

variable {n m : ℕ}

/-- The edge `(0 → 1) × {t}` of `Λ[n+2, 0] × Δ[m] ∪ Δ[n+2] × ∂Δ[m]`; it lies in the
piece `Λ[n+2, 0] × Δ[m]`. -/
def unionProdEdge₀₁ (n m : ℕ) (t : Fin (m + 1)) :
    (Subcomplex.unionProd Λ[n + 2, 0] ∂Δ[m] : SSet.{u}) _⦋1⦌ :=
  ⟨(stdSimplex.edge (n + 2) 0 1 (by simp), stdSimplex.edge m t t le_rfl),
    (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr (horn.edge₀₁ n).2)⟩

open Subcomplex.Pairing.RankFunction in
/-- No cell of the pairing of `Λ[n+2, 0] × Δ[m] ∪ Δ[n+2] × ∂Δ[m] ⊆ Δ[n+2] × Δ[m]` is a last
horn `Λ[d+1, d+1]`. -/
lemma cell_index_ne_last {j : ℕ}
    (c : (pairingCore.{u} (0 : Fin (n + 2)) m).pairing.rankFunction.Cell j) :
    c.index ≠ Fin.last _ := by
  obtain ⟨s, hs⟩ := c.exists_equivII
  intro H
  have h1 : (c.index : ℕ) = (s.index : ℕ) := c.index_val s hs
  have h2 : c.dim = s.d := c.dim_eq s hs
  have h3 : (c.index : ℕ) = c.dim + 1 := congrArg Fin.val H
  have h4 := s.index.isLt
  omega

/-- A type (I) simplex of index `0` starts with the step `(0, t) → (1, t)`. -/
lemma simplex_map_edge_of_index_eq_zero (s : pairingCore.Type₁.{u} (0 : Fin (n + 2)) m)
    (h0 : s.index = 0) (d : ℕ)
    (hd : d = s.d) (y : Δ[d + 1] _⦋1⦌) (hy : y = stdSimplex.edge (d + 1) 0 1 (by simp)) :
    ∃ t, (Δ[n + 2] ⊗ Δ[m]).map (stdSimplex.objEquiv y).op
      (_root_.cast (by subst hd; rfl) ((pairingCore (0 : Fin (n + 2)) m).simplex s)) =
      (stdSimplex.edge (n + 2) 0 1 (by simp), stdSimplex.edge m t t le_rfl) := by
  subst hd hy
  have hi := s.isIndex
  rw [h0, pairingCore.isIndex_succ] at hi
  refine ⟨(s.x.cast s.hd).simplex.2 0, ?_⟩
  erw [cast_eq]
  refine Prod.ext (stdSimplex.ext _ _ fun i ↦ ?_) (stdSimplex.ext _ _ fun i ↦ ?_)
  · fin_cases i
    · change (s.x.cast s.hd).simplex.1 0 = 0
      simpa using hi.1
    · change (s.x.cast s.hd).simplex.1 1 = 1
      simpa using hi.2.1
  · fin_cases i
    · rfl
    · change (s.x.cast s.hd).simplex.2 1 = (s.x.cast s.hd).simplex.2 0
      simpa using hi.2.2


open Subcomplex.Pairing.RankFunction in
/-- The attaching map of a cell of index `0` sends the initial edge `0 → 1` of its horn to an
edge `(0 → 1) × {t}`. -/
lemma cell_map_app_edge {j : ℕ}
    (c : (pairingCore.{u} (0 : Fin (n + 2)) m).pairing.rankFunction.Cell j) (hc : c.index = 0)
    (y : Δ[c.dim + 1] _⦋1⦌) (hy : y = stdSimplex.edge (c.dim + 1) 0 1 (by simp)) :
    ∃ t, c.map.app _ y =
      (stdSimplex.edge (n + 2) 0 1 (by simp), stdSimplex.edge m t t le_rfl) := by
  obtain ⟨s, hs⟩ := c.exists_equivII
  have h0 : s.index = 0 := by
    have h1 : (c.index : ℕ) = (s.index : ℕ) := c.index_val s hs
    rw [hc] at h1
    exact Fin.ext h1.symm
  rw [c.map_app s hs]
  exact simplex_map_edge_of_index_eq_zero s h0 c.dim (c.dim_eq s hs) y hy

open Subcomplex.Pairing.RankFunction Subcomplex in
/-- **The product cell lemma.** A map `Λ[n+2, 0] × Δ[m] ∪ Δ[n+2] × ∂Δ[m] ⟶ C` into a
quasicategory extends to `Δ[n+2] × Δ[m]` as soon as the edges `(0 → 1) × {t}` go to
equivalences. -/
theorem exists_extension_unionProd {C : SSet.{u}} [Quasicategory C]
    (H₀ : (Subcomplex.unionProd Λ[n + 2, 0] ∂Δ[m] : SSet.{u}) ⟶ C)
    (hH₀ : ∀ t, (Edge.mk' (H₀.app _ (unionProdEdge₀₁ n m t))).IsEquiv) :
    ∃ H : Δ[n + 2] ⊗ Δ[m] ⟶ C,
      (Subcomplex.unionProd Λ[n + 2, 0] ∂Δ[m]).ι ≫ H = H₀ := by
  -- spell the subcomplex as Mathlib's pairing does
  change (Subcomplex.unionProd Λ[n + 1 + 1, (0 : Fin (n + 2)).castSucc] ∂Δ[m] : SSet.{u}) ⟶ C
    at H₀
  show ∃ H : Δ[n + 1 + 1] ⊗ Δ[m] ⟶ C,
    (Subcomplex.unionProd Λ[n + 1 + 1, (0 : Fin (n + 2)).castSucc] ∂Δ[m]).ι ≫ H = H₀
  let f := (pairingCore.{u} (0 : Fin (n + 2)) m).pairing.rankFunction
  -- every cell can be filled, whatever the extension built so far
  have hfill : ∀ (j : ℕ) (c : f.Cell j) (v : (f.filtration j : SSet.{u}) ⟶ C),
      Subcomplex.homOfLE (f.le_filtration j) ≫ v = H₀ →
      ∃ σ : Δ[c.dim + 1] ⟶ C, c.mapHorn ≫ v = c.horn.ι ≫ σ := by
    intro j c v hv
    refine fill_horn_of_ne_last c.index (cell_index_ne_last c) (c.mapHorn ≫ v) ?_
    intro e hc he
    obtain ⟨t, ht⟩ := cell_map_app_edge c hc e.1 he
    have : (c.mapHorn ≫ v).app _ e = H₀.app _ (unionProdEdge₀₁ n m t) := by
      rw [← hv]
      change v.app _ (c.mapHorn.app _ e) = v.app _ ((homOfLE _).app _ _)
      congr 1
      exact Subtype.ext ht
    rw [this]
    exact hH₀ t
  -- the cellwise lifting principle, with target the terminal object
  obtain ⟨H, hH, -⟩ := f.exists_lift (terminal.from C) (terminal.from _) H₀
    (Subsingleton.elim _ _) fun j c v _ hv ↦
      (hfill j c v hv).imp fun _ hσ ↦ ⟨hσ.symm, Subsingleton.elim _ _⟩
  exact ⟨H, hH⟩

end prodStdSimplex

end SSet
