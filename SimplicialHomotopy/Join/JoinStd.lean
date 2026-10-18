/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Join.Join

/-!
# The join of standard simplices: `Δ[m] ⋆ Δ[n] ≅ Δ[m + n + 1]`

Kerodon Tag 0175 (Example 4.3.3.14) / [Lur09, Remark 1.2.8.2].

This is the computation that makes the join of `Join/Join.lean` usable: it is what lets
one read a simplex of a coslice `C_{f/}` (for `f : Δ[m] ⟶ C`) as an honest simplex of `C`, and it
is the first step of Kerodon's Lemma 4.3.6.16, which rewrites the outer horn `Λ[m + 2, m + 2]`
as a union inside `Δ[m] ⋆ Δ[1] ≅ Δ[m + 2]`.

The translation between the `aug`-model of `Join/Cone.lean` and monotone maps:

* `SSet.emptyOrderHom`, `SSet.orderHom_fin_zero_eq` (in `Join/Cone.lean`) : monotone maps
  out of `Fin 0` are unique.
* `SSet.stdSimplex.asOrderHom_map`, `map_objMk`, `eq_of_asOrderHom_eq` : the simplices of `Δ[N]`
  and their simplicial operators in terms of monotone maps.
* `SSet.stdSimplex.augOrderHom : (Δ[m] : SSet).aug j → (Fin j →o Fin (m + 1))` and its inverse
  `SSet.stdSimplex.augOfOrderHom`, with `augOrderHom_augMap` translating `SSet.augMap` into
  precomposition.

The iso itself is assembled from a pair of mutually inverse maps on simplices:

* `SSet.stdSimplex.joinToOrderHom` : an `q`-simplex `⟨j, k, x, y⟩` of `Δ[m] ⋆ Δ[n]` becomes the
  monotone map `Fin (q + 1) →o Fin (m + n + 2)` which is `x` on the initial `j` vertices and
  `m + 1 + y` on the final `k` vertices; `cut_joinToOrderHom` says its cut at `m + 1` recovers
  `j`.
* `SSet.stdSimplex.joinOfOrderHom` : the inverse, cutting a monotone map at `m + 1` by
  `SSet.cut`, `SSet.initialSeg` and `SSet.residual`.
* `SSet.stdSimplex.joinIso m n : join Δ[m] Δ[n] ≅ Δ[m + n + 1]`, with
  `joinIso_hom_joinInl` and `joinIso_hom_joinInr` identifying the two blocks with the front and
  back faces of `Δ[m + n + 1]`.
-/

universe u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet

namespace stdSimplex

/-! ### Standard simplices as monotone maps

Three lemmas of Mathlib's `Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean`, restated
through `asOrderHom` and `objMk` instead of `objEquiv` and morphisms of `SimplexCategory`. -/

/-- The simplicial operators of `Δ[N]` are precomposition, in terms of `asOrderHom`. Mathlib's
`SSet.stdSimplex.map_apply` is the same fact in terms of `objEquiv`. -/
lemma asOrderHom_map {N : ℕ} {q₁ q₂ : SimplexCategoryᵒᵖ} (ρ : q₁ ⟶ q₂)
    (α : (Δ[N] : SSet.{u}).obj q₁) :
    asOrderHom ((Δ[N] : SSet.{u}).map ρ α) = (asOrderHom α).comp ρ.unop.toOrderHom := rfl

/-- The simplicial operators of `Δ[N]` are precomposition, in terms of `objMk`. Mathlib's
`SSet.stdSimplex.map_objEquiv_symm` is the same fact in terms of `objEquiv.symm`. -/
lemma map_objMk {N : ℕ} {q₁ q₂ : SimplexCategoryᵒᵖ} (ρ : q₁ ⟶ q₂)
    (f : Fin ((unop q₁).len + 1) →o Fin (N + 1)) :
    (Δ[N] : SSet.{u}).map ρ (objMk f) = objMk (f.comp ρ.unop.toOrderHom) := rfl

/-- Two simplices of a standard simplex agreeing on vertices are equal. Mathlib has this as
`SSet.stdSimplex.ext`, for `Δ[n] _⦋d⦌` and vertex by vertex, and as the injectivity in
`SSet.stdSimplex.objMk_bijective`. -/
lemma eq_of_asOrderHom_eq {N : ℕ} {q : SimplexCategoryᵒᵖ} {α β : (Δ[N] : SSet.{u}).obj q}
    (h : asOrderHom α = asOrderHom β) : α = β :=
  congrArg objMk h

/-! ### `(Δ[m])⁺` in terms of monotone maps -/

/-- A simplex of `(Δ[m])⁺` in degree `j` is a monotone map `Fin j →o Fin (m + 1)`. -/
def augOrderHom {m : ℕ} : ∀ {j : ℕ}, (Δ[m] : SSet.{u}).aug j → (Fin j →o Fin (m + 1))
  | 0, _ => emptyOrderHom _
  | _ + 1, x => x.down.toOrderHom

/-- The inverse of `SSet.stdSimplex.augOrderHom`. -/
def augOfOrderHom {m : ℕ} : ∀ {j : ℕ}, (Fin j →o Fin (m + 1)) → (Δ[m] : SSet.{u}).aug j
  | 0, _ => PUnit.unit
  | _ + 1, f => ULift.up (Hom.mk f)

@[simp]
lemma augOrderHom_augOfOrderHom {m j : ℕ} (f : Fin j →o Fin (m + 1)) :
    augOrderHom.{u} (augOfOrderHom f) = f := by
  cases j with
  | zero => exact (orderHom_fin_zero_eq f).symm
  | succ _ => rfl

@[simp]
lemma augOfOrderHom_augOrderHom {m j : ℕ} (x : (Δ[m] : SSet.{u}).aug j) :
    augOfOrderHom (augOrderHom x) = x := by
  cases j with
  | zero => rfl
  | succ _ => rfl

/-- `SSet.augMap` becomes precomposition. -/
lemma augOrderHom_augMap {m a b : ℕ} (ρ : Fin a →o Fin b) (x : (Δ[m] : SSet.{u}).aug b) :
    augOrderHom ((Δ[m] : SSet.{u}).augMap ρ x) = (augOrderHom x).comp ρ := by
  cases a with
  | zero => exact (orderHom_fin_zero_eq _).trans (orderHom_fin_zero_eq _).symm
  | succ a =>
    cases b with
    | zero => exact (ρ 0).elim0
    | succ b => rfl

lemma eq_of_augOrderHom_eq {m j : ℕ} {x x' : (Δ[m] : SSet.{u}).aug j}
    (h : augOrderHom x = augOrderHom x') : x = x' := by
  rw [← augOfOrderHom_augOrderHom x, ← augOfOrderHom_augOrderHom x', h]

/-! ### Vertices as natural numbers

All the combinatorics below is phrased in terms of `SSet.stdSimplex.augVal`, which reads off the
`i`-th vertex of a simplex of `(Δ[m])⁺` as a natural number (and returns `0` out of range). This
keeps the dependent `Fin` proofs out of the statements, so that `omega` can be used freely. -/

/-- The `i`-th vertex of a simplex of `(Δ[m])⁺`, as a natural number (`0` out of range). -/
def augVal {m a : ℕ} (x : (Δ[m] : SSet.{u}).aug a) (i : ℕ) : ℕ :=
  if h : i < a then (augOrderHom x ⟨i, h⟩ : ℕ) else 0

lemma augVal_eq {m a : ℕ} (x : (Δ[m] : SSet.{u}).aug a) (i : ℕ) (h : i < a) :
    augVal x i = (augOrderHom x ⟨i, h⟩ : ℕ) :=
  dite_eq_left h

lemma augVal_lt {m a : ℕ} (x : (Δ[m] : SSet.{u}).aug a) {i : ℕ} (h : i < a) :
    augVal x i < m + 1 := by
  rw [augVal_eq x i h]
  exact (augOrderHom x ⟨i, h⟩).isLt

lemma augVal_mono {m a : ℕ} (x : (Δ[m] : SSet.{u}).aug a) {i i' : ℕ} (hii' : i ≤ i')
    (h' : i' < a) : augVal x i ≤ augVal x i' := by
  rw [augVal_eq x i (by omega), augVal_eq x i' h']
  exact Fin.le_def.1 ((augOrderHom x).monotone (Fin.le_def.2 hii'))

lemma augVal_augMap {m a b : ℕ} (ρ : Fin a →o Fin b) (x : (Δ[m] : SSet.{u}).aug b) {i : ℕ}
    (h : i < a) : augVal ((Δ[m] : SSet.{u}).augMap ρ x) i = augVal x (ρ ⟨i, h⟩) := by
  rw [augVal_eq _ i h, augOrderHom_augMap]
  exact (augVal_eq x _ (ρ ⟨i, h⟩).isLt).symm

lemma augVal_augOfOrderHom {m a : ℕ} (f : Fin a →o Fin (m + 1)) {i : ℕ} (h : i < a) :
    augVal (augOfOrderHom.{u} f) i = f ⟨i, h⟩ := by
  rw [augVal_eq _ i h, augOrderHom_augOfOrderHom]

/-- Two simplices of `(Δ[m])⁺` with the same vertices are equal (up to the `HEq` needed when the
degrees are only known to be equal). -/
lemma aug_heq_of_augVal {m a a' : ℕ} (ha : a = a') (x : (Δ[m] : SSet.{u}).aug a)
    (x' : (Δ[m] : SSet.{u}).aug a') (h : ∀ i, i < a → augVal x i = augVal x' i) : HEq x x' := by
  subst ha
  refine heq_of_eq (eq_of_augOrderHom_eq (OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_)))
  rw [← augVal_eq x i i.isLt, ← augVal_eq x' i i.isLt]
  exact h i i.isLt

/-! ### The join of two standard simplices -/

variable {m n : ℕ}

/-- The `i`-th vertex of a `q`-simplex of `Δ[m] ⋆ Δ[n]`, as a natural number: the `Δ[m]`-part on
the initial block of `j` vertices, and the `Δ[n]`-part shifted by `m + 1` on the final block. -/
def joinVal {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) (i : ℕ) : ℕ :=
  if i < s.j then augVal s.x i else m + 1 + augVal s.y (i - s.j)

lemma joinVal_of_lt {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) {i : ℕ} (h : i < s.j) :
    joinVal s i = augVal s.x i := ite_eq_left h

lemma joinVal_of_le {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) {i : ℕ} (h : s.j ≤ i) :
    joinVal s i = m + 1 + augVal s.y (i - s.j) := ite_eq_right (by omega)

lemma joinVal_lt {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) {i : ℕ} (hi : i < q + 1) :
    joinVal s i < m + n + 2 := by
  by_cases h : i < s.j
  · have := augVal_lt s.x h
    rw [joinVal_of_lt s h]; omega
  · have := augVal_lt s.y (show i - s.j < s.k by have := s.hjk; omega)
    rw [joinVal_of_le s (by omega)]; omega

lemma joinVal_lt_iff {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) (i : ℕ) :
    joinVal s i < m + 1 ↔ i < s.j := by
  by_cases h : i < s.j
  · simpa [joinVal_of_lt s h, h] using augVal_lt s.x h
  · rw [joinVal_of_le s (by omega)]
    simp only [h, iff_false, not_lt]
    omega

lemma joinVal_mono {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) {i i' : ℕ} (hii' : i ≤ i')
    (hi' : i' < q + 1) : joinVal s i ≤ joinVal s i' := by
  by_cases h : i < s.j
  · by_cases h' : i' < s.j
    · rw [joinVal_of_lt s h, joinVal_of_lt s h']
      exact augVal_mono s.x hii' h'
    · rw [joinVal_of_lt s h, joinVal_of_le s (i := i') (by omega)]
      have := augVal_lt s.x h
      omega
  · rw [joinVal_of_le s (i := i) (by omega), joinVal_of_le s (i := i') (by omega)]
    have := augVal_mono s.y (show i - s.j ≤ i' - s.j by omega)
      (show i' - s.j < s.k by have := s.hjk; omega)
    omega

/-- The monotone map `Fin (q + 1) →o Fin (m + n + 2)` attached to a `q`-simplex of
`Δ[m] ⋆ Δ[n]`. -/
def joinToOrderHom {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) :
    Fin (q + 1) →o Fin (m + n + 2) where
  toFun i := ⟨joinVal s (i : ℕ), joinVal_lt s i.isLt⟩
  monotone' _ _ h := Fin.le_def.2 (joinVal_mono s h (by omega))

@[simp]
lemma joinToOrderHom_apply {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) (i : Fin (q + 1)) :
    (joinToOrderHom s i : ℕ) = joinVal s (i : ℕ) := rfl

lemma cut_joinToOrderHom {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) :
    cut (joinToOrderHom s) (m + 1) = s.j := by
  refine Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (by have := s.hjk; omega) fun i ↦ ?_
  rw [lt_cut_iff, joinToOrderHom_apply]
  exact joinVal_lt_iff s _

/-- `SSet.JoinSimplex.map` is precomposition on vertices. -/
lemma joinVal_map {q q' : ℕ} (ρ : Fin (q' + 1) →o Fin (q + 1))
    (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) (i : Fin (q' + 1)) :
    joinVal (s.map ρ) (i : ℕ) = joinVal s (ρ i) := by
  have hcut := cut_le ρ s.j
  have hilt := i.isLt
  by_cases h : (i : ℕ) < cut ρ s.j
  · have hρ : (ρ i : ℕ) < s.j := (lt_cut_iff ρ s.j i).1 h
    rw [joinVal_of_lt (s.map ρ) (i := (i : ℕ)) (by rw [JoinSimplex.map_j]; omega),
      joinVal_of_lt s (i := (ρ i : ℕ)) hρ]
    show augVal ((Δ[m] : SSet.{u}).augMap (initialSeg ρ s.j) s.x) (i : ℕ) = augVal s.x (ρ i)
    rw [augVal_augMap _ _ h]
    exact congrArg (augVal s.x) (initialSeg_apply_val ρ s.j _)
  · have hρ : ¬ ((ρ i : ℕ) < s.j) := fun hc ↦ h ((lt_cut_iff ρ s.j i).2 hc)
    have hi : (i : ℕ) - cut ρ s.j < q' + 1 - cut ρ s.j := by omega
    have hlt : (i : ℕ) - cut ρ s.j + cut ρ s.j < q' + 1 := by omega
    rw [joinVal_of_le (s.map ρ) (i := (i : ℕ)) (by rw [JoinSimplex.map_j]; omega),
      joinVal_of_le s (i := (ρ i : ℕ)) (by omega)]
    show m + 1 + augVal ((Δ[n] : SSet.{u}).augMap (residual ρ s.j s.k s.hjk) s.y)
      ((i : ℕ) - cut ρ s.j) = m + 1 + augVal s.y ((ρ i : ℕ) - s.j)
    rw [augVal_augMap _ _ hi]
    have hfin : (⟨(i : ℕ) - cut ρ s.j + cut ρ s.j, hlt⟩ : Fin (q' + 1)) = i :=
      Fin.ext (show (i : ℕ) - cut ρ s.j + cut ρ s.j = (i : ℕ) from by omega)
    exact congrArg (fun t : Fin (q' + 1) ↦ m + 1 + augVal s.y ((ρ t : ℕ) - s.j)) hfin

/-- The `q`-simplex of `Δ[m] ⋆ Δ[n]` attached to a monotone map `Fin (q + 1) →o Fin (m + n + 2)`,
by cutting at `m + 1`. -/
def joinOfOrderHom {q : ℕ} (α : Fin (q + 1) →o Fin (m + n + 2)) :
    JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q where
  j := cut α (m + 1)
  k := q + 1 - cut α (m + 1)
  hjk := by have := cut_le α (m + 1); omega
  x := augOfOrderHom (initialSeg α (m + 1))
  y := augOfOrderHom (residual α (m + 1) (n + 1) (by omega))

lemma joinToOrderHom_joinOfOrderHom {q : ℕ} (α : Fin (q + 1) →o Fin (m + n + 2)) :
    joinToOrderHom (joinOfOrderHom.{u} (m := m) (n := n) α) = α := by
  refine OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_)
  rw [joinToOrderHom_apply]
  have hj : (joinOfOrderHom.{u} (m := m) (n := n) α).j = cut α (m + 1) := rfl
  have hcut := cut_le α (m + 1)
  have hilt := i.isLt
  by_cases h : (i : ℕ) < cut α (m + 1)
  · rw [joinVal_of_lt _ (i := (i : ℕ)) (by rw [hj]; omega)]
    show augVal (augOfOrderHom (initialSeg α (m + 1))) (i : ℕ) = (α i : ℕ)
    rw [augVal_augOfOrderHom _ h]
    exact initialSeg_apply_val α (m + 1) _
  · have hi : (i : ℕ) - cut α (m + 1) < q + 1 - cut α (m + 1) := by omega
    have hlt : (i : ℕ) - cut α (m + 1) + cut α (m + 1) < q + 1 := by omega
    have h1 : m + 1 ≤ (α i : ℕ) := not_lt.1 fun hc ↦ h ((lt_cut_iff α (m + 1) i).2 hc)
    have hfin : (⟨(i : ℕ) - cut α (m + 1) + cut α (m + 1), hlt⟩ : Fin (q + 1)) = i :=
      Fin.ext (show (i : ℕ) - cut α (m + 1) + cut α (m + 1) = (i : ℕ) from by omega)
    have h2 : (α ⟨(i : ℕ) - cut α (m + 1) + cut α (m + 1), hlt⟩ : ℕ) = (α i : ℕ) :=
      congrArg (fun t : Fin (q + 1) ↦ (α t : ℕ)) hfin
    rw [joinVal_of_le _ (i := (i : ℕ)) (by rw [hj]; omega)]
    show m + 1 + augVal (augOfOrderHom (residual α (m + 1) (n + 1) (by omega)))
      ((i : ℕ) - cut α (m + 1)) = (α i : ℕ)
    rw [augVal_augOfOrderHom _ hi, residual_apply_val, h2]
    omega

lemma joinOfOrderHom_joinToOrderHom {q : ℕ} (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) :
    joinOfOrderHom (joinToOrderHom s) = s := by
  have hj := cut_joinToOrderHom s
  have hk : q + 1 - cut (joinToOrderHom s) (m + 1) = s.k := by have := s.hjk; omega
  refine JoinSimplex.ext_of_j_eq hj ?_ ?_
  · refine aug_heq_of_augVal hj _ _ fun i hi ↦ ?_
    show augVal (augOfOrderHom (initialSeg (joinToOrderHom s) (m + 1))) i = augVal s.x i
    rw [augVal_augOfOrderHom _ hi]
    exact (initialSeg_apply_val (joinToOrderHom s) (m + 1) _).trans
      (joinVal_of_lt s (i := i) (by omega))
  · refine aug_heq_of_augVal hk _ _ fun i hi ↦ ?_
    have hlt : i + cut (joinToOrderHom s) (m + 1) < q + 1 := by omega
    show augVal (augOfOrderHom (residual (joinToOrderHom s) (m + 1) (n + 1) (by omega))) i
      = augVal s.y i
    rw [augVal_augOfOrderHom _ hi, residual_apply_val,
      show (joinToOrderHom s ⟨i + cut (joinToOrderHom s) (m + 1), hlt⟩ : ℕ)
        = joinVal s (i + cut (joinToOrderHom s) (m + 1)) from rfl,
      joinVal_of_le s (i := i + cut (joinToOrderHom s) (m + 1)) (by omega),
      show i + cut (joinToOrderHom s) (m + 1) - s.j = i from by omega]
    omega

/-! ### The isomorphism `Δ[m] ⋆ Δ[n] ≅ Δ[m + n + 1]` -/

/-- `SSet.stdSimplex.joinToOrderHom` turns `SSet.JoinSimplex.map` into precomposition. -/
lemma joinToOrderHom_map {q q' : ℕ} (ρ : Fin (q' + 1) →o Fin (q + 1))
    (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q) :
    joinToOrderHom (s.map ρ) = (joinToOrderHom s).comp ρ :=
  OrderHom.ext _ _ (funext fun i ↦ Fin.ext (joinVal_map ρ s i))

lemma eq_of_joinToOrderHom_eq {q : ℕ} {s s' : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] q}
    (h : joinToOrderHom s = joinToOrderHom s') : s = s' := by
  rw [← joinOfOrderHom_joinToOrderHom s, ← joinOfOrderHom_joinToOrderHom s', h]

/-- The comparison map `Δ[m] ⋆ Δ[n] ⟶ Δ[m + n + 1]`. -/
def joinHom (m n : ℕ) : join (Δ[m] : SSet.{u}) Δ[n] ⟶ Δ[m + n + 1] where
  app _ := ↾fun s ↦ objMk (joinToOrderHom s)
  naturality q₁ q₂ ρ := ConcreteCategory.hom_ext _ _
    fun (s : JoinSimplex (Δ[m] : SSet.{u}) Δ[n] (unop q₁).len) ↦ by
      show objMk (joinToOrderHom (JoinSimplex.map ρ.unop.toOrderHom s)) =
        (Δ[m + n + 1] : SSet.{u}).map ρ (objMk (joinToOrderHom s))
      rw [joinToOrderHom_map, map_objMk]

/-- The inverse comparison map `Δ[m + n + 1] ⟶ Δ[m] ⋆ Δ[n]`. -/
def joinInv (m n : ℕ) : (Δ[m + n + 1] : SSet.{u}) ⟶ join (Δ[m] : SSet.{u}) Δ[n] where
  app _ := ↾fun α ↦ joinOfOrderHom (asOrderHom α)
  naturality q₁ q₂ ρ := ConcreteCategory.hom_ext _ _ fun α ↦ by
    show joinOfOrderHom (asOrderHom ((Δ[m + n + 1] : SSet.{u}).map ρ α)) =
      JoinSimplex.map ρ.unop.toOrderHom (joinOfOrderHom (asOrderHom α))
    refine eq_of_joinToOrderHom_eq ?_
    rw [joinToOrderHom_map, joinToOrderHom_joinOfOrderHom, joinToOrderHom_joinOfOrderHom,
      asOrderHom_map]

/-- **Kerodon 0175**: the join of two standard simplices is a standard simplex. -/
@[simps]
def joinIso (m n : ℕ) : join (Δ[m] : SSet.{u}) Δ[n] ≅ Δ[m + n + 1] where
  hom := joinHom m n
  inv := joinInv m n
  hom_inv_id := by
    ext q s
    exact joinOfOrderHom_joinToOrderHom s
  inv_hom_id := by
    ext q α
    exact eq_of_asOrderHom_eq (joinToOrderHom_joinOfOrderHom (asOrderHom α))

/-! ### The two blocks -/

/-- The vertices of `SSet.JoinSimplex.inl`. -/
lemma joinVal_inl {q : ℕ} (x : (Δ[m] : SSet.{u}) _⦋q⦌) {i : ℕ} (h : i < q + 1) :
    joinVal (JoinSimplex.inl (B := (Δ[n] : SSet.{u})) x) i = (asOrderHom x ⟨i, h⟩ : ℕ) := by
  rw [joinVal_of_lt _ h]
  exact augVal_eq (a := q + 1) x i h

/-- The vertices of `SSet.JoinSimplex.inr`. -/
lemma joinVal_inr {q : ℕ} (y : (Δ[n] : SSet.{u}) _⦋q⦌) {i : ℕ} (h : i < q + 1) :
    joinVal (JoinSimplex.inr (A := (Δ[m] : SSet.{u})) y) i = m + 1 + (asOrderHom y ⟨i, h⟩ : ℕ) := by
  rw [joinVal_of_le _ (Nat.zero_le i)]
  exact congrArg (fun t ↦ m + 1 + t) (augVal_eq (a := q + 1) y i h)

/-- The front inclusion `Fin (m + 1) →o Fin (m + n + 2)`, `i ↦ i`. -/
def frontOrderHom (m n : ℕ) : Fin (m + 1) →o Fin (m + n + 2) where
  toFun := Fin.castLE (by omega)
  monotone' _ _ h := h

/-- The back inclusion `Fin (n + 1) →o Fin (m + n + 2)`, `i ↦ m + 1 + i`. -/
def backOrderHom (m n : ℕ) : Fin (n + 1) →o Fin (m + n + 2) where
  toFun i := ⟨m + 1 + i, by have := i.isLt; omega⟩
  monotone' _ _ h := Fin.mk_le_mk.2 (by have := Fin.le_def.1 h; omega)

/-- The `A`-block of `Δ[m] ⋆ Δ[n] ≅ Δ[m + n + 1]` is the front face. -/
lemma joinIso_hom_joinInl (m n : ℕ) :
    joinInl (Δ[m] : SSet.{u}) Δ[n] ≫ (joinIso m n).hom =
      SSet.stdSimplex.map (mkHom (frontOrderHom m n)) := by
  ext q x
  refine eq_of_asOrderHom_eq (OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_))
  exact joinVal_inl x i.isLt

/-- The `B`-block of `Δ[m] ⋆ Δ[n] ≅ Δ[m + n + 1]` is the back face. -/
lemma joinIso_hom_joinInr (m n : ℕ) :
    joinInr (Δ[m] : SSet.{u}) Δ[n] ≫ (joinIso m n).hom =
      SSet.stdSimplex.map (mkHom (backOrderHom m n)) := by
  ext q y
  refine eq_of_asOrderHom_eq (OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_))
  exact joinVal_inr y i.isLt

end stdSimplex

end SSet
