/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank

/-!
# The spine of a standard simplex is inner anodyne

* `SSet.stdSimplex.spineSubcomplex n : Δ[n].Subcomplex` : the spine `Sp[n] = ⋃ᵢ Δ[{i, i+1}] ⊆ Δ[n]`.
* `SSet.stdSimplex.spineCore n : (spineSubcomplex (n + 1)).PairingCore` : a regular inner pairing
  (in the sense of Moss) for the spine: a nondegenerate simplex `S ⊆ [n + 1]` of `Δ[n + 1]`
  not in the spine (i.e. `|S| ≥ 2` and `S ≠ {a, a + 1}`) is of type (I) if `a + 1 ∈ S`
  (`a = min S`), of type (II) otherwise; the partner of a type (II) simplex `S` is
  `S ∪ {a + 1}`, of which `S` is the face `δ 1`.
* `SSet.innerAnodyneExtensions_spineSubcomplex_ι n :
  innerAnodyneExtensions (spineSubcomplex (n + 1)).ι`
  ([Kerodon, Example 1.5.7.7, Tag 00JA(a)], from Prop. 1.5.7.3 (Tag 00J6) and
  Thm. 1.5.7.1 (Tag 00J4); or [Joyal]. Note `spineSubcomplex 0 = ⊥ ≠ Δ[0]`, hence the shift.)
* `SSet.rlp_monomorphisms_pre_spineSubcomplex_ι_app` : for a quasicategory `C`, the restriction
  `Fun(Δ[n + 1], C) ⟶ Fun(Sp[n + 1], C)` is a trivial fibration.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Limits
  MorphismProperty Simplicial

namespace SSet

namespace stdSimplex

/-- The spine `Sp[n] ⊆ Δ[n]`, the union of the edges `Δ[{i, i + 1}]`. -/
def spineSubcomplex (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ i : Fin n, face {i.castSucc, i.succ}

lemma face_le_spineSubcomplex {n : ℕ} (i : Fin n) :
    face {i.castSucc, i.succ} ≤ spineSubcomplex.{u} n :=
  le_iSup (fun i : Fin n ↦ face.{u} {i.castSucc, i.succ}) i

lemma spineSubcomplex_le_top (n : ℕ) : spineSubcomplex.{u} n ≤ ⊤ := le_top

@[simp]
lemma spineSubcomplex_zero : spineSubcomplex.{u} 0 = ⊥ := by
  simp [spineSubcomplex]

lemma mem_spineSubcomplex_iff {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (spineSubcomplex n).obj _ ↔ ∃ i : Fin n, ∀ j, x j = i.castSucc ∨ x j = i.succ := by
  simp [spineSubcomplex, Subfunctor.iSup_obj]

/-- Every vertex of `Δ[n + 1]` lies in the spine. -/
lemma vertex_mem_spineSubcomplex {n : ℕ} (x : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
    x ∈ (spineSubcomplex (n + 1)).obj _ := by
  rw [mem_spineSubcomplex_iff]
  by_cases h : (x 0).val < n + 1
  · exact ⟨⟨(x 0).val, h⟩, fun j ↦ Or.inl (by rw [Fin.fin_one_eq_zero j]; ext; rfl)⟩
  · exact ⟨⟨n, by omega⟩, fun j ↦ Or.inr (by
      rw [Fin.fin_one_eq_zero j]; ext; simp only [Fin.val_succ]; omega)⟩

/-- An edge `[a, a + 1]` of `Δ[n]` lies in the spine. -/
lemma edge_mem_spineSubcomplex {n : ℕ} (x : (Δ[n] : SSet.{u}) _⦋1⦌)
    (hx : (x 1).val = (x 0).val + 1) :
    x ∈ (spineSubcomplex n).obj _ := by
  rw [mem_spineSubcomplex_iff]
  refine ⟨⟨(x 0).val, by have := (x 1).isLt; omega⟩, fun j ↦ ?_⟩
  fin_cases j
  · exact Or.inl (by ext; rfl)
  · exact Or.inr (by ext; simp [hx])

/-- The spine has no simplices of dimension `≥ 2` besides degenerate ones: a nondegenerate
`(d + 2)`-simplex of `Δ[n]` is not in the spine. -/
lemma notMem_spineSubcomplex_of_nonDegenerate {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 2⦌)
    (hx : x ∈ Δ[n].nonDegenerate _) :
    x ∉ (spineSubcomplex n).obj _ := by
  rw [mem_nonDegenerate_iff_strictMono] at hx
  rw [mem_spineSubcomplex_iff]
  rintro ⟨i, hi⟩
  have h₀ := hx (show (0 : Fin (d + 3)) < 1 from Fin.zero_lt_one)
  have h₁ := hx (show (1 : Fin (d + 3)) < 2 by
    rw [Fin.lt_def, Fin.val_one, Fin.val_two]; omega)
  rw [Fin.lt_def] at h₀ h₁
  have := hi 0
  have := hi 1
  have := hi 2
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  omega

/-- A nondegenerate edge `[a, b]` of `Δ[n]` with `b ≥ a + 2` is not in the spine. -/
lemma notMem_spineSubcomplex_of_two_le {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌)
    (hx : (x 0).val + 2 ≤ (x 1).val) :
    x ∉ (spineSubcomplex n).obj _ := by
  rw [mem_spineSubcomplex_iff]
  rintro ⟨i, hi⟩
  have := hi 0
  have := hi 1
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  omega

/-! ### The face `δ 1` and its inverse "insertion" operation -/

lemma δ_one_apply_zero {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 2⦌) :
    Δ[n].δ 1 x 0 = x 0 := by
  rw [δ_apply, Fin.one_succAbove_zero]

lemma δ_one_apply_succ {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 2⦌) (j : Fin (d + 1)) :
    Δ[n].δ 1 x j.succ = x j.succ.succ := by
  rw [δ_apply, Fin.one_succAbove_succ]

lemma δ_one_apply_one {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 2⦌) :
    Δ[n].δ 1 x 1 = x 2 := by
  rw [δ_apply, Fin.one_succAbove_one]

lemma δ_zero_apply {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌) (j : Fin (d + 1)) :
    Δ[n].δ 0 x j = x j.succ := by
  rw [δ_apply, Fin.succAbove_zero]

lemma δ_succ_succ_apply_zero {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 2⦌) (i : Fin (d + 1)) :
    Δ[n].δ i.succ.succ x 0 = x 0 := by
  rw [δ_apply, Fin.succ_succAbove_zero]

lemma δ_succ_succ_apply_one {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 2⦌) (i : Fin (d + 1)) :
    Δ[n].δ i.succ.succ x 1 = x 1 := by
  rw [δ_apply, ← Fin.succ_zero_eq_one, Fin.succ_succAbove_succ, Fin.succ_succAbove_zero,
    Fin.succ_zero_eq_one]

/-- Two nondegenerate simplices `y, y'` of `Δ[n]` with `y 1 = y 0 + 1` and `y' 1 = y' 0 + 1`
having the same face `δ 1` are equal. -/
lemma eq_of_δ_one_eq {n d : ℕ} {y y' : (Δ[n] : SSet.{u}) _⦋d + 2⦌}
    (hy : (y 1).val = (y 0).val + 1) (hy' : (y' 1).val = (y' 0).val + 1)
    (h : Δ[n].δ 1 y = Δ[n].δ 1 y') : y = y' := by
  apply stdSimplex.ext
  intro i
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · have := DFunLike.congr_fun h 0
    simpa only [δ_one_apply_zero] using this
  · obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · have h0 := DFunLike.congr_fun h 0
      simp only [δ_one_apply_zero] at h0
      ext
      rw [Fin.succ_zero_eq_one, hy, hy', h0]
    · have := DFunLike.congr_fun h i.succ
      simpa only [δ_one_apply_succ] using this

/-- Inserting the vertex `x 0 + 1` in position `1` of a simplex `x` of `Δ[n]`
with `x 1 ≥ x 0 + 2` (as a function `Fin (d + 3) → Fin (n + 1)`). -/
def insertSuccFun {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌) (hx : (x 0).val + 2 ≤ (x 1).val) :
    Fin (d + 3) → Fin (n + 1) :=
  Fin.cons (x 0) (Fin.cons ⟨(x 0).val + 1, by have := (x 1).isLt; omega⟩
    (fun k : Fin (d + 1) ↦ x k.succ))

lemma strictMono_insertSuccFun {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌)
    (hx : (x 0).val + 2 ≤ (x 1).val) (hx' : x ∈ Δ[n].nonDegenerate _) :
    StrictMono (insertSuccFun x hx) := by
  rw [mem_nonDegenerate_iff_strictMono] at hx'
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · simp [insertSuccFun, Fin.lt_def]
  · rw [← Fin.succ_castSucc]
    simp only [insertSuccFun, Fin.cons_succ]
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ k
    · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.lt_def, Fin.succ_zero_eq_one]
      omega
    · rw [← Fin.succ_castSucc]
      simp only [Fin.cons_succ]
      exact hx' (by simp)

/-- Inserting the vertex `x 0 + 1` in position `1` of a nondegenerate simplex `x` of `Δ[n]`
with `x 1 ≥ x 0 + 2`: this is the type (I) simplex paired with `x`. -/
def insertSucc {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌) (hx : (x 0).val + 2 ≤ (x 1).val)
    (hx' : x ∈ Δ[n].nonDegenerate _) : (Δ[n] : SSet.{u}) _⦋d + 2⦌ :=
  objMk ⟨insertSuccFun x hx, (strictMono_insertSuccFun x hx hx').monotone⟩

lemma insertSucc_apply_zero {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌)
    (hx : (x 0).val + 2 ≤ (x 1).val) (hx' : x ∈ Δ[n].nonDegenerate _) :
    insertSucc x hx hx' 0 = x 0 := by
  simp [insertSucc, insertSuccFun]

lemma insertSucc_apply_one {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌)
    (hx : (x 0).val + 2 ≤ (x 1).val) (hx' : x ∈ Δ[n].nonDegenerate _) :
    (insertSucc x hx hx' 1).val = (x 0).val + 1 := by
  rw [← Fin.succ_zero_eq_one]
  simp [insertSucc, insertSuccFun]

lemma insertSucc_apply_succ_succ {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌)
    (hx : (x 0).val + 2 ≤ (x 1).val) (hx' : x ∈ Δ[n].nonDegenerate _) (k : Fin (d + 1)) :
    insertSucc x hx hx' k.succ.succ = x k.succ := by
  simp [insertSucc, insertSuccFun]

lemma insertSucc_mem_nonDegenerate {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌)
    (hx : (x 0).val + 2 ≤ (x 1).val) (hx' : x ∈ Δ[n].nonDegenerate _) :
    insertSucc x hx hx' ∈ Δ[n].nonDegenerate _ := by
  rw [mem_nonDegenerate_iff_strictMono]
  exact strictMono_insertSuccFun x hx hx'

lemma δ_one_insertSucc {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d + 1⦌)
    (hx : (x 0).val + 2 ≤ (x 1).val) (hx' : x ∈ Δ[n].nonDegenerate _) :
    Δ[n].δ 1 (insertSucc x hx hx') = x := by
  apply stdSimplex.ext
  intro j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · rw [δ_one_apply_zero, insertSucc_apply_zero]
  · rw [δ_one_apply_succ, insertSucc_apply_succ_succ]

/-! ### The pairing for the spine -/

/-- The index type of the pairing for the spine of `Δ[n]`: the type (I) simplices, i.e. the
nondegenerate simplices `y` of dimension `≥ 2` with `y 1 = y 0 + 1`. -/
structure SpineIndex (n : ℕ) where
  /-- the dimension of the type (II) simplex, minus one -/
  d : ℕ
  /-- the type (I) simplex -/
  y : (Δ[n] : SSet.{u}) _⦋d + 2⦌
  nonDegenerate : y ∈ Δ[n].nonDegenerate _
  succ_eq : (y 1).val = (y 0).val + 1

namespace SpineIndex

variable {n : ℕ} (s : SpineIndex.{u} n)

lemma strictMono : StrictMono s.y :=
  (mem_nonDegenerate_iff_strictMono _).1 s.nonDegenerate

lemma zero_lt_one : (s.y 0).val < (s.y 1).val :=
  s.strictMono Fin.zero_lt_one

lemma one_lt_two : (s.y 1).val < (s.y 2).val :=
  s.strictMono (show (1 : Fin (s.d + 3)) < 2 by rw [Fin.lt_def, Fin.val_one, Fin.val_two]; omega)

lemma δ_one_mem_nonDegenerate : Δ[n].δ 1 s.y ∈ Δ[n].nonDegenerate _ := by
  rw [mem_nonDegenerate_iff_strictMono]
  intro a b h
  rw [δ_apply, δ_apply]
  exact s.strictMono (Fin.strictMono_succAbove _ h)

end SpineIndex

/-- The Moss pairing for the spine `Sp[n + 1] ⊆ Δ[n + 1]`: a type (II) simplex is a
nondegenerate simplex `x` of dimension `≥ 1` with `x 1 ≥ x 0 + 2`; its partner is the
type (I) simplex `insertSucc x`, of which `x` is the face `δ 1`. -/
@[simps]
def spineCore (n : ℕ) : (spineSubcomplex.{u} (n + 1)).PairingCore where
  ι := SpineIndex.{u} (n + 1)
  dim s := s.d + 1
  simplex s := s.y
  index _ := 1
  nonDegenerate₁ s := s.nonDegenerate
  nonDegenerate₂ s := s.δ_one_mem_nonDegenerate
  notMem₁ s := notMem_spineSubcomplex_of_nonDegenerate s.y s.nonDegenerate
  notMem₂ s := notMem_spineSubcomplex_of_two_le (Δ[n + 1].δ 1 s.y) (by
    rw [δ_one_apply_zero, δ_one_apply_one]
    have := s.zero_lt_one
    have := s.one_lt_two
    omega)
  injective_type₁' {s t} h := by
    obtain ⟨ds, y, hy, hy'⟩ := s
    obtain ⟨dt, y', hy₁, hy₁'⟩ := t
    have hd : ds + 2 = dt + 2 := S.dim_eq_of_mk_eq h
    obtain rfl : ds = dt := by omega
    obtain rfl := (S.ext_iff _ _).1 h
    rfl
  injective_type₂' {s t} h := by
    obtain ⟨ds, y, hy, hy'⟩ := s
    obtain ⟨dt, y', hy₁, hy₁'⟩ := t
    have hd : ds + 1 = dt + 1 := S.dim_eq_of_mk_eq h
    obtain rfl : ds = dt := by omega
    obtain rfl := eq_of_δ_one_eq hy' hy₁' ((S.ext_iff _ _).1 h)
    rfl
  type₁_ne_type₂' s t h := by
    obtain ⟨ds, y, hy, hy'⟩ := s
    obtain ⟨dt, y', hy₁, hy₁'⟩ := t
    have hd : ds + 2 = dt + 1 := S.dim_eq_of_mk_eq h
    obtain rfl : dt = ds + 1 := by omega
    have h' : y = Δ[n + 1].δ 1 y' := (S.ext_iff _ _).1 h
    have h0 : y 0 = y' 0 := by simpa only [δ_one_apply_zero] using DFunLike.congr_fun h' 0
    have h1 : y 1 = y' 2 := by simpa only [δ_one_apply_one] using DFunLike.congr_fun h' 1
    have h01 : (y' 0).val < (y' 1).val := (SpineIndex.mk _ y' hy₁ hy₁').zero_lt_one
    have h12 : (y' 1).val < (y' 2).val := (SpineIndex.mk _ y' hy₁ hy₁').one_lt_two
    have e0 := congrArg Fin.val h0
    have e1 := congrArg Fin.val h1
    omega
  surjective' x := by
    obtain ⟨m, x, hx, hx', rfl⟩ := Subcomplex.N.mk_surjective x
    cases m with
    | zero => exact (hx' (vertex_mem_spineSubcomplex x)).elim
    | succ m =>
      by_cases h : (x 1).val = (x 0).val + 1
      · cases m with
        | zero => exact (hx' (edge_mem_spineSubcomplex x h)).elim
        | succ m => exact ⟨⟨m, x, hx, h⟩, Or.inl rfl⟩
      · have h' : (x 0).val + 2 ≤ (x 1).val := by
          have := (mem_nonDegenerate_iff_strictMono x).1 hx Fin.zero_lt_one
          rw [Fin.lt_def] at this
          omega
        exact ⟨⟨m, insertSucc x h' hx, insertSucc_mem_nonDegenerate x h' hx,
          insertSucc_apply_one x h' hx⟩, Or.inr (congrArg S.mk (δ_one_insertSucc x h' hx).symm)⟩

instance (n : ℕ) : (spineCore.{u} n).IsInner where
  ne_zero (s : SpineIndex.{u} (n + 1)) := by
    show (1 : Fin (s.d + 3)) ≠ 0
    exact Fin.ne_of_val_ne (by simp)
  ne_last (s : SpineIndex.{u} (n + 1)) := by
    show (1 : Fin (s.d + 3)) ≠ Fin.last (s.d + 2)
    intro h
    rw [Fin.ext_iff, Fin.val_one, Fin.val_last] at h
    omega

/-- A weak rank function for `spineCore n`: the rank of a type (I) simplex `y` is
`n + 1 - y 0` (the ancestrality relation forces the first vertex to increase). -/
def spineCoreWeakRankFunction (n : ℕ) : (spineCore.{u} n).WeakRankFunction ℕ where
  rank s := n + 1 - (s.y 0).val
  lt {s t} hst hd := by
    obtain ⟨hne, hlt⟩ := hst
    obtain ⟨ds, y, hy, hy'⟩ := s
    obtain ⟨dt, y', hy₁, hy₁'⟩ := t
    obtain rfl : ds = dt := by simpa using hd
    have hle := Subcomplex.N.le_iff.1 hlt.le
    rw [SSet.N.le_iff_exists_mono] at hle
    obtain ⟨f, hf, hδ⟩ := hle
    obtain ⟨i, rfl⟩ := @SimplexCategory.eq_δ_of_mono (ds + 1) f hf
    change Δ[n + 1].δ i y' = Δ[n + 1].δ 1 y at hδ
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ i
    · have h0 := DFunLike.congr_fun hδ 0
      rw [δ_zero_apply, δ_one_apply_zero, Fin.succ_zero_eq_one] at h0
      have := (y' 1).isLt
      dsimp
      rw [← h0]
      omega
    · obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · exact (hne (by obtain rfl := eq_of_δ_one_eq hy₁' hy' hδ; rfl)).elim
      · have h0 := DFunLike.congr_fun hδ 0
        have h1 := DFunLike.congr_fun hδ 1
        rw [δ_succ_succ_apply_zero, δ_one_apply_zero] at h0
        rw [δ_succ_succ_apply_one, δ_one_apply_one] at h1
        have h01 : (y 0).val < (y 1).val := (SpineIndex.mk _ y hy hy').zero_lt_one
        have h12 : (y 1).val < (y 2).val := (SpineIndex.mk _ y hy hy').one_lt_two
        rw [h0, h1] at hy₁'
        omega

instance (n : ℕ) : (spineCore.{u} n).IsRegular :=
  (spineCoreWeakRankFunction n).isRegular

end stdSimplex

/-- The spine inclusion `Sp[n + 1] ↪ Δ[n + 1]` is a (strong) inner anodyne extension. -/
theorem strongInnerAnodyneExtensions_spineSubcomplex_ι (n : ℕ) :
    strongInnerAnodyneExtensions (stdSimplex.spineSubcomplex.{u} (n + 1)).ι :=
  (stdSimplex.spineCore n).pairing.strongInnerAnodyneExtensions

/-- The spine inclusion `Sp[n + 1] ↪ Δ[n + 1]` is inner anodyne. -/
theorem innerAnodyneExtensions_spineSubcomplex_ι (n : ℕ) :
    innerAnodyneExtensions (stdSimplex.spineSubcomplex.{u} (n + 1)).ι :=
  (stdSimplex.spineCore n).pairing.innerAnodyneExtensions

/-- The spine inclusion `Sp[n] ↪ Δ[n]` is inner anodyne for `n ≥ 1`. -/
theorem innerAnodyneExtensions_spineSubcomplex_ι_of_pos (n : ℕ) (hn : 0 < n) :
    innerAnodyneExtensions (stdSimplex.spineSubcomplex.{u} n).ι := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact innerAnodyneExtensions_spineSubcomplex_ι n

/-- For a quasicategory `C`, the restriction `Fun(Δ[n + 1], C) ⟶ Fun(Sp[n + 1], C)` along the
spine inclusion is a trivial fibration (it has the right lifting property with respect to all
monomorphisms). -/
theorem rlp_monomorphisms_pre_spineSubcomplex_ι_app (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    (MorphismProperty.monomorphisms SSet).rlp
      ((MonoidalClosed.pre (stdSimplex.spineSubcomplex (n + 1)).ι).app C) := by
  intro A B j hj
  have : Mono j := hj
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet)
    (stdSimplex.spineSubcomplex (n + 1)).ι j
  let sq₁₃ := Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom
    (stdSimplex.spineSubcomplex (n + 1)).ι (terminal.from C) terminalIsTerminal
  change HasLiftingProperty j sq₁₃.π
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂ sq₁₃]
  exact innerAnodyneExtensions_pushoutObjObjι' sq₁₂ (innerAnodyneExtensions_spineSubcomplex_ι n) _
    (mem_innerFibrations _)

end SSet
