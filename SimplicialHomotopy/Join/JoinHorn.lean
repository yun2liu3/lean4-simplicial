/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Horn.HornEdge
import SimplicialHomotopy.Join.JoinStd

/-!
# Horns of a join

Kerodon Lemma 4.3.6.16 (Tag 018N), second assertion: inside `Δ[p] ⋆ Δ[n+1] ≅ Δ[p+n+2]` the
horn at a *back* vertex `i` is the union

`(Δ[p] ⋆ Λ[n+1, i]) ∪ (∂Δ[p] ⋆ Δ[n+1])`.

For `n = 0` and `i = 1` this is Kerodon's `Λ[p+2, p+2] = (Δ[p] ⋆ {1}) ∪ (∂Δ[p] ⋆ Δ[1])`, the
combinatorial input of Kerodon 01H0 (Proposition 4.4.2.13); for `i < n + 1` the horn is *inner*,
which is the generating case of the join form of [Lur09, 2.1.2.3].

* `SSet.Subcomplex.joinSub A₀ B₀` : the join `A₀ ⋆ B₀` as a subcomplex of `A ⋆ B`.
* `SSet.stdSimplex.preimage_horn_joinIso` : the identity above, as an equality of subcomplexes of
  `Δ[p] ⋆ Δ[n+1]` (the horn pulled back along `SSet.stdSimplex.joinIso`).
* `SSet.stdSimplex.preimage_horn_last` : the case that Kerodon 01H0 uses, `Λ[p+2, p+2]`.

Everything is proved on vertices, through the ℕ-valued `SSet.stdSimplex.joinVal` of
`Join/JoinStd.lean` and the membership bridges `augMem_boundary_iff`, `augMem_face_one_iff`,
`augMem_horn_of_notMem` / `exists_notMem_of_augMem_horn` and `mem_horn_iff_exists_val`.
-/

universe u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet

namespace Subcomplex

variable {A B : SSet.{u}}

/-- `A₀ ⋆ B₀` as a subcomplex of `A ⋆ B`: the simplices whose two blocks lie in `A₀` and `B₀`. -/
def joinSub (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) : (join A B).Subcomplex where
  obj _ := {s | A₀.augMem s.x ∧ B₀.augMem s.y}
  map _ _ hs := ⟨A₀.augMem_augMap _ hs.1, B₀.augMem_augMap _ hs.2⟩

lemma mem_joinSub_iff (A₀ : A.Subcomplex) (B₀ : B.Subcomplex) {q : SimplexCategoryᵒᵖ}
    (s : (join A B).obj q) :
    s ∈ (joinSub A₀ B₀).obj q ↔ A₀.augMem s.x ∧ B₀.augMem s.y := Iff.rfl

lemma joinSub_top_top : joinSub (⊤ : A.Subcomplex) (⊤ : B.Subcomplex) = ⊤ :=
  le_antisymm le_top fun _ _ _ ↦ ⟨augMem_top _, augMem_top _⟩

lemma joinSub_mono {A₀ A₁ : A.Subcomplex} {B₀ B₁ : B.Subcomplex} (hA : A₀ ≤ A₁) (hB : B₀ ≤ B₁) :
    joinSub A₀ B₀ ≤ joinSub A₁ B₁ :=
  fun _ _ hs ↦ ⟨augMem_mono hA hs.1, augMem_mono hB hs.2⟩

end Subcomplex

/-! ### Augmented membership in the boundary and in a vertex -/

namespace stdSimplex

/-- A simplex of `(Δ[m])⁺` lies in `(∂Δ[m])⁺` exactly when it misses a vertex. -/
lemma augMem_boundary_iff {m k : ℕ} (x : (Δ[m] : SSet.{u}).aug k) :
    (boundary m).augMem x ↔ ∃ v : ℕ, v < m + 1 ∧ ∀ i, i < k → augVal x i ≠ v := by
  cases k with
  | zero =>
    exact iff_of_true trivial ⟨0, by omega, fun i hi ↦ absurd hi (by omega)⟩
  | succ k =>
    have key : ∀ y : (Δ[m] : SSet.{u}) _⦋k⦌, y ∈ (boundary m).obj (op ⦋k⦌) ↔
        ∃ v : ℕ, v < m + 1 ∧ ∀ i, i < k + 1 → augVal (m := m) (a := k + 1) y i ≠ v := by
      intro y
      rw [mem_boundary_iff_notMem_range]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨(v : ℕ), v.isLt, fun i hi hval ↦ hv ⟨⟨i, hi⟩, ?_⟩⟩
        exact Fin.ext ((augVal_eq (m := m) (a := k + 1) y i hi).symm.trans hval)
      · rintro ⟨v, hv, h⟩
        refine ⟨⟨v, hv⟩, ?_⟩
        rintro ⟨i, hi⟩
        exact h (i : ℕ) i.isLt
          ((augVal_eq (m := m) (a := k + 1) y (i : ℕ) i.isLt).trans (congrArg Fin.val hi))
    exact key x

/-- A simplex of `(Δ[1])⁺` lies in `({1})⁺` exactly when all its vertices are `1`. -/
lemma augMem_face_one_iff {k : ℕ} (y : (Δ[1] : SSet.{u}).aug k) :
    (face {1}).augMem y ↔ ∀ i, i < k → augVal y i = 1 := by
  cases k with
  | zero => exact iff_of_true trivial fun i hi ↦ absurd hi (by omega)
  | succ k =>
    have key : ∀ z : (Δ[1] : SSet.{u}) _⦋k⦌, z ∈ (face {1}).obj (op ⦋k⦌) ↔
        ∀ i, i < k + 1 → augVal (m := 1) (a := k + 1) z i = 1 := by
      intro z
      rw [mem_face_iff]
      constructor
      · intro h i hi
        exact (augVal_eq (m := 1) (a := k + 1) z i hi).trans
          (congrArg Fin.val (Finset.mem_singleton.1 (h ⟨i, hi⟩)))
      · intro h i
        refine Finset.mem_singleton.2 (Fin.ext ?_)
        exact ((augVal_eq (m := 1) (a := k + 1) z (i : ℕ) i.isLt).symm.trans
          (h (i : ℕ) i.isLt))
    exact key y

/-- Membership in a horn, in terms of a missed vertex, as an equation between naturals: the
ℕ-valued form of Mathlib's `SSet.mem_horn_iff_notMem_range`, stated for an arbitrary
`q : SimplexCategoryᵒᵖ`. -/
lemma mem_horn_iff_exists_val {n : ℕ} (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (x : (Δ[n] : SSet.{u}).obj q) :
    x ∈ (horn n i).obj q ↔
      ∃ v : ℕ, v < n + 1 ∧ v ≠ (i : ℕ) ∧ ∀ t, (asOrderHom x t : ℕ) ≠ v := by
  rw [mem_horn_iff, Ne, Set.eq_univ_iff_forall]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := not_forall.1 h
    refine ⟨(v : ℕ), v.isLt, fun hvi ↦ hv (Or.inr (Fin.ext hvi)), fun t ht ↦ hv (Or.inl ⟨t, ?_⟩)⟩
    exact Fin.ext ht
  · rintro ⟨v, hv, hvi, h⟩ hall
    rcases hall ⟨v, hv⟩ with hr | hi
    · obtain ⟨t, ht⟩ := hr
      exact h t (congrArg Fin.val ht)
    · exact hvi (congrArg Fin.val hi)

/-- A simplex of `(Δ[n])⁺` that misses a vertex `w ≠ i` lies in `(Λ[n, i])⁺`. -/
lemma augMem_horn_of_notMem {n k : ℕ} {i : Fin (n + 1)} (y : (Δ[n] : SSet.{u}).aug k)
    (w : ℕ) (hw : w < n + 1) (hwi : w ≠ (i : ℕ)) (h : ∀ t, t < k → augVal y t ≠ w) :
    (horn n i).augMem y := by
  cases k with
  | zero => trivial
  | succ k =>
    have key : ∀ z : (Δ[n] : SSet.{u}) _⦋k⦌,
        (∀ t, t < k + 1 → augVal (m := n) (a := k + 1) z t ≠ w) →
          z ∈ (horn n i).obj (op ⦋k⦌) := by
      intro z hz
      refine (mem_horn_iff_exists_val i z).2 ⟨w, hw, hwi, fun t hval ↦ ?_⟩
      exact hz (t : ℕ) t.isLt
        ((augVal_eq (m := n) (a := k + 1) z (t : ℕ) t.isLt).trans hval)
    exact key y h

/-- Conversely, a simplex of `(Δ[n])⁺` of positive degree lying in `(Λ[n, i])⁺` misses some
vertex `w ≠ i`. -/
lemma exists_notMem_of_augMem_horn {n k : ℕ} {i : Fin (n + 1)}
    (y : (Δ[n] : SSet.{u}).aug (k + 1)) (hy : (horn n i).augMem y) :
    ∃ w : ℕ, w < n + 1 ∧ w ≠ (i : ℕ) ∧ ∀ t, t < k + 1 → augVal y t ≠ w := by
  have key : ∀ z : (Δ[n] : SSet.{u}) _⦋k⦌, z ∈ (horn n i).obj (op ⦋k⦌) →
      ∃ w : ℕ, w < n + 1 ∧ w ≠ (i : ℕ) ∧
        ∀ t, t < k + 1 → augVal (m := n) (a := k + 1) z t ≠ w := by
    intro z hz
    obtain ⟨w, hw, hwi, h⟩ := (mem_horn_iff_exists_val i z).1 hz
    exact ⟨w, hw, hwi, fun t ht hval ↦ h ⟨t, ht⟩
      ((augVal_eq (m := n) (a := k + 1) z t ht).symm.trans hval)⟩
  exact key y hy

/-! ### The horn identity -/

/-- Membership in the pullback of a horn at a back vertex along `joinIso`, as a missed vertex. -/
lemma mem_preimage_horn_iff (p n : ℕ) (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (s : (join (Δ[p] : SSet.{u}) Δ[n]).obj q) :
    s ∈ ((horn (p + n + 1) (backOrderHom p n i)).preimage (joinIso p n).hom).obj q ↔
      ∃ v : ℕ, v < p + n + 2 ∧ v ≠ p + 1 + (i : ℕ) ∧
        ∀ t, t < q.unop.len + 1 → joinVal s t ≠ v := by
  refine Iff.trans
    (mem_horn_iff_exists_val (backOrderHom p n i) ((joinIso p n).hom.app q s)) ?_
  constructor
  · rintro ⟨v, hv, hvi, h⟩
    exact ⟨v, hv, hvi, fun t ht hval ↦ h ⟨t, ht⟩ hval⟩
  · rintro ⟨v, hv, hvi, h⟩
    exact ⟨v, hv, hvi, fun t hval ↦ h (t : ℕ) t.isLt hval⟩

/-- **Kerodon 4.3.6.16** (Tag 018N), second assertion: under `Δ[p] ⋆ Δ[n+1] ≅ Δ[p+n+2]`, the
horn at the back vertex `i` is `(Δ[p] ⋆ Λ[n+1, i]) ∪ (∂Δ[p] ⋆ Δ[n+1])`.
For `i ≠ Fin.last _` the horn is inner. -/
theorem preimage_horn_joinIso (p n : ℕ) (i : Fin (n + 1 + 1)) :
    (horn (p + (n + 1) + 1) (backOrderHom p (n + 1) i)).preimage (joinIso p (n + 1)).hom =
      Subcomplex.joinSub (⊤ : (Δ[p] : SSet.{u}).Subcomplex) (horn (n + 1) i) ⊔
        Subcomplex.joinSub (boundary p) (⊤ : (Δ[n + 1] : SSet.{u}).Subcomplex) := by
  refine le_antisymm (fun q s hs ↦ ?_) (fun q s hs ↦ ?_)
  · obtain ⟨v, hv, hvi, h⟩ := (mem_preimage_horn_iff p (n + 1) i s).1 hs
    by_cases hvp : v < p + 1
    · refine Or.inr ⟨(augMem_boundary_iff s.x).2 ⟨v, hvp, fun t ht ↦ ?_⟩,
        Subcomplex.augMem_top _⟩
      have hne := h t (by have := s.hjk; omega)
      rwa [joinVal_of_lt s ht] at hne
    · refine Or.inl ⟨Subcomplex.augMem_top _,
        augMem_horn_of_notMem s.y (v - (p + 1)) (by omega) (by omega) fun t ht ↦ ?_⟩
      have hlt : t + s.j < q.unop.len + 1 := by have := s.hjk; omega
      have hne := h (t + s.j) hlt
      rw [joinVal_of_le s (Nat.le_add_left _ _), show t + s.j - s.j = t from by omega] at hne
      omega
  · rw [mem_preimage_horn_iff]
    rcases hs with hs | hs
    · obtain ⟨w, hw, hwi, hwy⟩ : ∃ w : ℕ, w < n + 2 ∧ w ≠ (i : ℕ) ∧
          ∀ t, t < s.k → augVal s.y t ≠ w := by
        obtain ⟨j, k, hjk, x, y⟩ := s
        cases k with
        | zero =>
          exact ⟨if (i : ℕ) = 0 then 1 else 0, by split <;> omega, by split <;> omega,
            fun t ht ↦ absurd ht (Nat.not_lt_zero t)⟩
        | succ k => exact exists_notMem_of_augMem_horn y hs.2
      refine ⟨p + 1 + w, by omega, by omega, fun t ht hval ↦ ?_⟩
      by_cases hj : t < s.j
      · rw [joinVal_of_lt s hj] at hval
        have := augVal_lt s.x hj
        omega
      · rw [joinVal_of_le s (by omega)] at hval
        exact hwy (t - s.j) (by have := s.hjk; omega) (by omega)
    · obtain ⟨v, hv, hb⟩ := (augMem_boundary_iff s.x).1 hs.1
      refine ⟨v, by omega, by omega, fun t ht hval ↦ ?_⟩
      by_cases hj : t < s.j
      · exact hb t hj ((joinVal_of_lt s hj).symm.trans hval)
      · rw [joinVal_of_le s (by omega)] at hval
        omega

/-- The case of **Kerodon 4.3.6.16** used in the proof of Kerodon 4.4.2.13 (Tag 01H0): under
`Δ[m] ⋆ Δ[1] ≅ Δ[m+2]` the outer horn `Λ[m+2, m+2]` is the union
`(Δ[m] ⋆ {1}) ∪ (∂Δ[m] ⋆ Δ[1])`. -/
theorem preimage_horn_last (m : ℕ) :
    (horn (m + 1 + 1) (Fin.last (m + 1 + 1))).preimage (joinIso m 1).hom =
      Subcomplex.joinSub (⊤ : (Δ[m] : SSet.{u}).Subcomplex) (face {1}) ⊔
        Subcomplex.joinSub (boundary m) (⊤ : (Δ[1] : SSet.{u}).Subcomplex) := by
  rw [← horn_one_one_eq_face]
  exact preimage_horn_joinIso m 0 (Fin.last 1)

end stdSimplex

end SSet
