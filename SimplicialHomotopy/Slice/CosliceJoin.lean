/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Slice.Coslice
import SimplicialHomotopy.Join.JoinStd

/-!
# The universal property of the coslice `X_{f/}`

For `f : X _⦋p⦌` the coslice of `Slice/Coslice.lean` is characterised by
`Hom(K, X_{f/}) ≃ {F : Δ[p] ⋆ K ⟶ X // (Δ[p] ⟶ Δ[p] ⋆ K ⟶ X) = f}` (Kerodon 0189,
[Lur09, §1.2.9]); this is the `p`-fold generalisation of `SSet.coneHomEquiv` in
`Join/Cone.lean`.

Main results:

* `SSet.cosliceHomEquiv K X f` : the bijection above, with
  `SSet.joinInr_comp_toJoin` (`joinInr ≫ ĝ = g ≫ X.cosliceProj f`) and
  `SSet.toJoin_naturality` (naturality in `K`).

The arithmetic core:

* `SSet.augDeg p k` : the degree of the simplex of `X` attached to an augmented degree `k`,
  namely `p` for `k = 0` and `p + 1 + (k - 1)` otherwise.
* `SSet.pShift p ρ` : the `p`-shift `Fin (augDeg p a + 1) →o Fin (augDeg p b + 1)` of
  `ρ : Fin a →o Fin b`, the identity on the front `p + 1` vertices; it is
  `SimplexCategory.shiftFun` when `a` and `b` are both positive and the front inclusion
  `SimplexCategory.castAddOrderHom` when `a = 0`.
* `SSet.joinCollapse p s` : for a `q`-simplex `s` of `Δ[p] ⋆ K`, the map
  `Fin (q + 1) →o Fin (augDeg p s.k + 1)` which is `s.x` on the front block and the identity
  (shifted) on the back block. This is the generalisation of `SSet.collapse`.
* `SSet.joinCollapse_map` : the compatibility of `joinCollapse` with `SSet.JoinSimplex.map`,
  generalising `SSet.augShift_residual_comp_collapse`.
* `SSet.joinCons p y` : the simplex `id_{Δ[p]} ⋆ y` of `Δ[p] ⋆ K`, together with its three
  transport lemmas `joinCons_map_shiftFun`, `joinCons_map_castAddOrderHom` and
  `joinCons_map_joinCollapseOf`; every simplex of `Δ[p] ⋆ K` is a face of one of these.

All the arithmetic is stated in *component form* (`SSet.joinCollapseOf`, `SSet.toJoinFunOf`):
a lemma mentioning `s.map ρ` must take the components `j`, `k`, `hjk`, `x`, `y` and the
reindexing proof as explicit arguments, because `(s.map ρ).k` is only definitionally
`q' + 1 - cut ρ s.j` and `rw` cannot cross that gap. The structure-form corollaries
(`SSet.joinCollapse`, `SSet.toJoinFun`) are then one-line `exact`s.
-/

universe u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet

/-! ### The degree attached to an augmented degree -/

/-- The degree of the simplex of `X` attached to an augmented degree `k` over a `p`-simplex. -/
def augDeg (p : ℕ) : ℕ → ℕ
  | 0 => p
  | k + 1 => p + 1 + k

@[simp] lemma augDeg_zero (p : ℕ) : augDeg p 0 = p := rfl

@[simp] lemma augDeg_succ (p k : ℕ) : augDeg p (k + 1) = p + 1 + k := rfl

lemma augDeg_add_one_eq (p k : ℕ) : augDeg p k + 1 = p + 1 + k := by
  cases k <;> rfl

/-! ### The `p`-shift of a monotone map -/

/-- The `p`-shift of `ρ : Fin a →o Fin b`: the identity on the front `p + 1` vertices and `ρ`
on the remaining ones. -/
def pShift (p : ℕ) : ∀ {a b : ℕ}, (Fin a →o Fin b) → (Fin (augDeg p a + 1) →o Fin (augDeg p b + 1))
  | 0, 0, _ => OrderHom.id
  | 0, _ + 1, _ => castAddOrderHom p _
  | _ + 1, 0, ρ => (ρ 0).elim0
  | _ + 1, _ + 1, ρ => shiftFun p ρ

lemma pShift_apply_of_lt (p : ℕ) {a b : ℕ} (ρ : Fin a →o Fin b) (i : Fin (augDeg p a + 1))
    (hi : (i : ℕ) < p + 1) : (pShift p ρ i : ℕ) = i := by
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | succ b => rfl
  | succ a =>
    cases b with
    | zero => exact (ρ 0).elim0
    | succ b =>
      exact congrArg Fin.val (shiftFun_castAdd p ρ ⟨(i : ℕ), hi⟩)

lemma pShift_apply_of_le (p : ℕ) {a b : ℕ} (ρ : Fin a →o Fin b) (i : Fin (augDeg p a + 1))
    (hi : p + 1 ≤ (i : ℕ)) (h : (i : ℕ) - (p + 1) < a) :
    (pShift p ρ i : ℕ) = p + 1 + (ρ ⟨(i : ℕ) - (p + 1), h⟩ : ℕ) := by
  cases a with
  | zero => exact absurd h (by omega)
  | succ a =>
    cases b with
    | zero => exact (ρ 0).elim0
    | succ b =>
      have he : (Fin.natAdd (p + 1) ⟨(i : ℕ) - (p + 1), h⟩ : Fin (p + 1 + (a + 1))) = i :=
        Fin.ext (by simp only [Fin.val_natAdd]; omega)
      calc (pShift p ρ i : ℕ)
          = ((shiftFun p ρ (Fin.natAdd (p + 1) ⟨(i : ℕ) - (p + 1), h⟩) : Fin _) : ℕ) :=
            congrArg (fun t : Fin (p + 1 + (a + 1)) ↦ ((shiftFun p ρ t : Fin _) : ℕ)) he.symm
        _ = p + 1 + (ρ ⟨(i : ℕ) - (p + 1), h⟩ : ℕ) := by
            rw [shiftFun_natAdd]
            simp

lemma pShift_zero_zero (p : ℕ) (ρ : Fin 0 →o Fin 0) : pShift p ρ = OrderHom.id := rfl

lemma pShift_zero_succ (p b : ℕ) (ρ : Fin 0 →o Fin (b + 1)) :
    pShift p ρ = castAddOrderHom p b := rfl

lemma pShift_succ_succ (p a b : ℕ) (ρ : Fin (a + 1) →o Fin (b + 1)) :
    pShift p ρ = shiftFun p ρ := rfl

/-! ### The collapse map of a simplex of `Δ[p] ⋆ K` -/

variable {K : SSet.{u}}

/-- The vertices of `SSet.joinCollapse`: `s.x` on the front block, the identity (shifted by
`p + 1`) on the back block. -/
def joinCollapseVal (p : ℕ) {j : ℕ} (x : (Δ[p] : SSet.{u}).aug j) (i : ℕ) : ℕ :=
  if i < j then stdSimplex.augVal x i else p + 1 + (i - j)

lemma joinCollapseVal_of_lt (p : ℕ) {j : ℕ} (x : (Δ[p] : SSet.{u}).aug j) {i : ℕ} (h : i < j) :
    joinCollapseVal p x i = stdSimplex.augVal x i := ite_eq_left h

lemma joinCollapseVal_of_le (p : ℕ) {j : ℕ} (x : (Δ[p] : SSet.{u}).aug j) {i : ℕ} (h : j ≤ i) :
    joinCollapseVal p x i = p + 1 + (i - j) := ite_eq_right (by omega)

lemma joinCollapseVal_lt (p : ℕ) {j k q : ℕ} (hjk : j + k = q + 1)
    (x : (Δ[p] : SSet.{u}).aug j) {i : ℕ} (hi : i < q + 1) :
    joinCollapseVal p x i < augDeg p k + 1 := by
  rw [augDeg_add_one_eq]
  by_cases h : i < j
  · rw [joinCollapseVal_of_lt p x h]
    have := stdSimplex.augVal_lt x h
    omega
  · rw [joinCollapseVal_of_le p x (by omega)]
    omega

lemma joinCollapseVal_mono (p : ℕ) {j : ℕ} (x : (Δ[p] : SSet.{u}).aug j) {i i' : ℕ}
    (hii' : i ≤ i') : joinCollapseVal p x i ≤ joinCollapseVal p x i' := by
  by_cases h : i < j
  · by_cases h' : i' < j
    · rw [joinCollapseVal_of_lt p x h, joinCollapseVal_of_lt p x h']
      exact stdSimplex.augVal_mono x hii' h'
    · rw [joinCollapseVal_of_lt p x h, joinCollapseVal_of_le p x (by omega)]
      have := stdSimplex.augVal_lt x h
      omega
  · rw [joinCollapseVal_of_le p x (by omega), joinCollapseVal_of_le p x (by omega)]
    omega

/-- For a decomposition `j + k = q + 1` of the vertices with front simplex `x`, the monotone map
`Fin (q + 1) →o Fin (augDeg p k + 1)` which is `x` on the front block and the identity (shifted by
`p + 1`) on the back block. This generalises `SSet.collapse` (the case `p = 0`).

It is stated in terms of the components `j`, `k`, `x` rather than of a simplex `s` of `Δ[p] ⋆ K`
because the arithmetic lemmas below have to talk about `s.map ρ`, whose degree `q' + 1 - cut ρ j`
would then be hidden behind a structure projection: `rw` cannot cross that gap. -/
def joinCollapseOf (p : ℕ) {q j k : ℕ} (hjk : j + k = q + 1) (x : (Δ[p] : SSet.{u}).aug j) :
    Fin (q + 1) →o Fin (augDeg p k + 1) where
  toFun i := ⟨joinCollapseVal p x (i : ℕ), joinCollapseVal_lt p hjk x i.isLt⟩
  monotone' _ _ h := Fin.le_def.2 (joinCollapseVal_mono p x (Fin.le_def.1 h))

@[simp]
lemma joinCollapseOf_apply_val (p : ℕ) {q j k : ℕ} (hjk : j + k = q + 1)
    (x : (Δ[p] : SSet.{u}).aug j) (i : Fin (q + 1)) :
    (joinCollapseOf p hjk x i : ℕ) = joinCollapseVal p x (i : ℕ) := rfl

/-- The collapse map of a `q`-simplex `s` of `Δ[p] ⋆ K`. -/
def joinCollapse (p : ℕ) {q : ℕ} (s : JoinSimplex (Δ[p] : SSet.{u}) K q) :
    Fin (q + 1) →o Fin (augDeg p s.k + 1) :=
  joinCollapseOf p s.hjk s.x

@[simp]
lemma joinCollapse_apply_val (p : ℕ) {q : ℕ} (s : JoinSimplex (Δ[p] : SSet.{u}) K q)
    (i : Fin (q + 1)) : (joinCollapse p s i : ℕ) = joinCollapseVal p s.x (i : ℕ) := rfl

/-- The compatibility of the collapse map with reindexing: generalises
`SSet.augShift_residual_comp_collapse`. -/
lemma joinCollapseOf_map (p : ℕ) {q q' j k : ℕ} (hjk : j + k = q + 1)
    (x : (Δ[p] : SSet.{u}).aug j) (ρ : Fin (q' + 1) →o Fin (q + 1))
    (h' : cut ρ j + (q' + 1 - cut ρ j) = q' + 1) (i : Fin (q' + 1)) :
    (pShift p (residual ρ j k hjk)
        (joinCollapseOf p h' ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x) i) : ℕ) =
      joinCollapseOf p hjk x (ρ i) := by
  have hcut := cut_le ρ j
  have hilt := i.isLt
  by_cases h : (i : ℕ) < cut ρ j
  · have hρ : (ρ i : ℕ) < j := (lt_cut_iff ρ j i).1 h
    have hlt : (joinCollapseOf p h' ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x) i : ℕ) <
        p + 1 := by
      rw [joinCollapseOf_apply_val, joinCollapseVal_of_lt p _ h]
      exact stdSimplex.augVal_lt _ h
    refine Eq.trans (pShift_apply_of_lt p _ _ hlt) ?_
    show joinCollapseVal p ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x) (i : ℕ) =
      joinCollapseVal p x (ρ i)
    rw [joinCollapseVal_of_lt p _ h, joinCollapseVal_of_lt p x hρ,
      stdSimplex.augVal_augMap _ _ h]
    exact congrArg (stdSimplex.augVal x) (initialSeg_apply_val ρ j _)
  · have hρ : ¬ ((ρ i : ℕ) < j) := fun hc ↦ h ((lt_cut_iff ρ j i).2 hc)
    have hval : (joinCollapseOf p h' ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x) i : ℕ) =
        p + 1 + ((i : ℕ) - cut ρ j) := by
      rw [joinCollapseOf_apply_val, joinCollapseVal_of_le p _ (by omega)]
    have hge :
        p + 1 ≤ (joinCollapseOf p h' ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x) i : ℕ) := by
      rw [hval]; omega
    have hsub : (joinCollapseOf p h' ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x) i : ℕ) -
        (p + 1) < q' + 1 - cut ρ j := by rw [hval]; omega
    refine Eq.trans (pShift_apply_of_le p _ _ hge hsub) ?_
    have h2 : (⟨(joinCollapseOf p h' ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x) i : ℕ) -
        (p + 1), hsub⟩ : Fin (q' + 1 - cut ρ j)) = ⟨(i : ℕ) - cut ρ j, by omega⟩ :=
      Fin.ext (by
        show (joinCollapseOf p h' ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x) i : ℕ) - (p + 1) =
          (i : ℕ) - cut ρ j
        omega)
    have hfin : (⟨(i : ℕ) - cut ρ j + cut ρ j, by omega⟩ : Fin (q' + 1)) = i :=
      Fin.ext (show (i : ℕ) - cut ρ j + cut ρ j = (i : ℕ) from by omega)
    have key : (residual ρ j k hjk
        ⟨(joinCollapseOf p h' ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x) i : ℕ) - (p + 1),
          hsub⟩ : ℕ) = (ρ i : ℕ) - j := by
      rw [h2, residual_apply_val]
      exact congrArg (fun t : Fin (q' + 1) ↦ (ρ t : ℕ) - j) hfin
    refine Eq.trans (congrArg (fun t ↦ p + 1 + t) key) ?_
    exact (joinCollapseVal_of_le p x (show j ≤ (ρ i : ℕ) by omega)).symm

/-- `SSet.joinCollapseOf_map` for a simplex of `Δ[p] ⋆ K`. -/
lemma joinCollapse_map (p : ℕ) {q q' : ℕ} (ρ : Fin (q' + 1) →o Fin (q + 1))
    (s : JoinSimplex (Δ[p] : SSet.{u}) K q) (i : Fin (q' + 1)) :
    (pShift p (residual ρ s.j s.k s.hjk) (joinCollapse p (s.map ρ) i) : ℕ) =
      joinCollapse p s (ρ i) :=
  joinCollapseOf_map p s.hjk s.x ρ (s.map ρ).hjk i

/-! ### The two blocks -/

/-- `joinCollapseVal` lands in the front block exactly on the front vertices. -/
lemma joinCollapseVal_lt_iff (p : ℕ) {j : ℕ} (x : (Δ[p] : SSet.{u}).aug j) (i : ℕ) :
    joinCollapseVal p x i < p + 1 ↔ i < j := by
  by_cases h : i < j
  · simp only [joinCollapseVal_of_lt p x h, h, iff_true]
    exact stdSimplex.augVal_lt x h
  · rw [joinCollapseVal_of_le p x (by omega)]
    simp only [h, iff_false, not_lt]
    omega

/-- The collapse map of a simplex in the image of `joinInl` is the simplex itself. -/
lemma mkHom_joinCollapseOf_top {p n : ℕ} (x : (Δ[p] : SSet.{u}) _⦋n⦌) :
    mkHom (joinCollapseOf p (k := 0) (Nat.add_zero (n + 1)) x) = stdSimplex.objEquiv x :=
  Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ Fin.ext
    ((joinCollapseVal_of_lt p (j := n + 1) x i.isLt).trans
      (stdSimplex.augVal_eq (a := n + 1) x (i : ℕ) i.isLt))))

/-- The collapse map of a simplex in the image of `joinInr` is the back block inclusion. -/
lemma mkHom_joinCollapseOf_zero (p n : ℕ) :
    mkHom (joinCollapseOf p (j := 0) (k := n + 1) (Nat.zero_add (n + 1))
      (PUnit.unit : (Δ[p] : SSet.{u}).aug 0)) = backHom p n :=
  Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ Fin.ext
    ((joinCollapseVal_of_le p (j := 0) (x := (PUnit.unit : (Δ[p] : SSet.{u}).aug 0))
        (Nat.zero_le _)).trans
      (by
        show p + 1 + ((i : ℕ) - 0) = ((Fin.natAdd (p + 1) i : Fin (p + 1 + (n + 1))) : ℕ)
        rw [Fin.val_natAdd]
        omega))))

/-! ### The front identity simplex -/

/-- The identity simplex `stdSimplex.idSimplex p` of `Δ[p]`, as a simplex of `(Δ[p])⁺` in
degree `p + 1`. -/
def idAug (p : ℕ) : (Δ[p] : SSet.{u}).aug (p + 1) :=
  stdSimplex.idSimplex p

lemma augVal_idAug (p : ℕ) {i : ℕ} (h : i < p + 1) : stdSimplex.augVal (idAug.{u} p) i = i :=
  stdSimplex.augVal_augOfOrderHom OrderHom.id h

lemma objEquiv_idAug (p : ℕ) :
    stdSimplex.objEquiv (idAug.{u} p : (Δ[p] : SSet.{u}) _⦋p⦌) = 𝟙 ⦋p⦌ := rfl

/-- `SSet.pShift_apply_of_lt` for `SimplexCategory.shiftFun`. -/
lemma _root_.SimplexCategory.shiftFun_val_of_lt (p : ℕ) {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (i : Fin (p + 1 + (m + 1))) (hi : (i : ℕ) < p + 1) : (shiftFun p f i : ℕ) = (i : ℕ) :=
  pShift_apply_of_lt p f i hi

/-- `SSet.pShift_apply_of_le` for `SimplexCategory.shiftFun`. -/
lemma _root_.SimplexCategory.shiftFun_val_of_le (p : ℕ) {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (i : Fin (p + 1 + (m + 1))) (hi : p + 1 ≤ (i : ℕ)) (h : (i : ℕ) - (p + 1) < m + 1) :
    (shiftFun p f i : ℕ) = p + 1 + (f ⟨(i : ℕ) - (p + 1), h⟩ : ℕ) :=
  pShift_apply_of_le p f i hi h

/-- The simplex `id_{Δ[p]} ⋆ y` of `Δ[p] ⋆ K`, in degree `p + 1 + n`. -/
def joinCons (p : ℕ) {n : ℕ} (y : K _⦋n⦌) : JoinSimplex (Δ[p] : SSet.{u}) K (p + 1 + n) :=
  ⟨p + 1, n + 1, rfl, idAug p, y⟩

lemma cut_shiftFun (p : ℕ) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    cut (shiftFun p (m := m) (n := n) α) (p + 1) = p + 1 :=
  Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (Nat.le_succ_of_le (Nat.le_add_right _ _)) fun i ↦ by
    rw [lt_cut_iff]
    exact Fin.addCases (motive := fun t : Fin (p + 1 + (m + 1)) ↦
        ((shiftFun p (m := m) (n := n) α t : ℕ) < p + 1 ↔ (t : ℕ) < p + 1))
      (fun t ↦ by simp only [shiftFun_castAdd, Fin.val_castAdd])
      (fun t ↦ by simp only [shiftFun_natAdd, Fin.val_natAdd]; omega) i

lemma cut_castAddOrderHom (p n : ℕ) : cut (castAddOrderHom p n) (p + 1) = p + 1 :=
  Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (by omega) fun i ↦ by
    rw [lt_cut_iff]
    exact ⟨fun _ ↦ i.isLt, fun _ ↦ i.isLt⟩

/-- `joinCons` is natural: `(id ⋆ α)* (id ⋆ y) = id ⋆ α* y`. -/
lemma joinCons_map_shiftFun (p : ℕ) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (y : K _⦋n⦌) :
    (joinCons p y).map (shiftFun p (m := m) (n := n) α) =
      joinCons p (K.map (mkHom α).op y) := by
  have hc := cut_shiftFun p α
  refine JoinSimplex.ext_of_j_eq hc ?_ ?_
  · refine stdSimplex.aug_heq_of_augVal hc _ _ (fun i hi ↦ ?_)
    have hip : i < p + 1 := hc ▸ hi
    exact ((stdSimplex.augVal_augMap _ (idAug p) hi).trans
      ((augVal_idAug p (Fin.isLt _)).trans
        ((initialSeg_apply_val (shiftFun p (m := m) (n := n) α) (p + 1) _).trans
          (shiftFun_val_of_lt p α _ hip)))).trans (augVal_idAug p hip).symm
  · have ha : p + 1 + (m + 1) - cut (shiftFun p (m := m) (n := n) α) (p + 1) = m + 1 := by
      rw [hc]; omega
    refine HEq.trans (augMap_congr K ha
      (residual (shiftFun p (m := m) (n := n) α) (p + 1) (n + 1) rfl)
      α (fun i ↦ ?_) y) (heq_of_eq rfl)
    have hi : (i : ℕ) < m + 1 := by have := i.isLt; omega
    rw [residual_apply_val]
    have h2 : (⟨(i : ℕ) + cut (shiftFun p (m := m) (n := n) α) (p + 1),
        by have := i.isLt; omega⟩ : Fin (p + 1 + (m + 1))) = Fin.natAdd (p + 1) ⟨(i : ℕ), hi⟩ :=
      Fin.ext (by simp [hc]; omega)
    rw [h2, shiftFun_natAdd, Fin.val_natAdd, Nat.add_sub_cancel_left]
    rfl

/-- The front face of `id_{Δ[p]} ⋆ y` is the identity `p`-simplex. -/
lemma joinCons_map_castAddOrderHom (p : ℕ) {n : ℕ} (y : K _⦋n⦌) :
    (joinCons p y).map (castAddOrderHom p n) =
      JoinSimplex.inl (B := K) (idAug.{u} p : (Δ[p] : SSet.{u}) _⦋p⦌) := by
  have hc := cut_castAddOrderHom p n
  refine JoinSimplex.ext_of_j_eq hc ?_ ?_
  · refine stdSimplex.aug_heq_of_augVal hc _ _ (fun i hi ↦ ?_)
    have hip : i < p + 1 := hc ▸ hi
    exact ((stdSimplex.augVal_augMap _ (idAug p) hi).trans
      ((augVal_idAug p (Fin.isLt _)).trans
        (initialSeg_apply_val (castAddOrderHom p n) (p + 1) _))).trans (augVal_idAug p hip).symm
  · refine HEq.trans (augMap_congr K (a' := 0) (by omega)
      (residual (castAddOrderHom p n) (p + 1) (n + 1) rfl) (emptyOrderHom (n + 1))
      (fun i ↦ absurd i.isLt (by omega)) y) (heq_of_eq rfl)

/-- The collapse map applied to `id_{Δ[p]} ⋆ y` recovers the simplex. -/
lemma joinCons_map_joinCollapseOf (p : ℕ) {q j k : ℕ} (hjk : j + (k + 1) = q + 1)
    (x : (Δ[p] : SSet.{u}).aug j) (y : K _⦋k⦌) :
    (joinCons p y).map (joinCollapseOf p hjk x) = ⟨j, k + 1, hjk, x, y⟩ := by
  have hc : cut (joinCollapseOf p hjk x) (p + 1) = j :=
    Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (by omega) fun i ↦ by
      rw [lt_cut_iff, joinCollapseOf_apply_val]
      exact joinCollapseVal_lt_iff p x (i : ℕ)
  refine JoinSimplex.ext_of_j_eq hc ?_ ?_
  · refine stdSimplex.aug_heq_of_augVal hc _ _ (fun i hi ↦ ?_)
    have hij : i < j := hc ▸ hi
    exact (stdSimplex.augVal_augMap _ (idAug p) hi).trans
      ((augVal_idAug p (Fin.isLt _)).trans
        ((initialSeg_apply_val (joinCollapseOf p hjk x) (p + 1) _).trans
          (joinCollapseVal_of_lt p x hij)))
  · have ha : q + 1 - cut (joinCollapseOf p hjk x) (p + 1) = k + 1 := by rw [hc]; omega
    refine HEq.trans (augMap_congr K ha
      (residual (joinCollapseOf p hjk x) (p + 1) (k + 1) (augDeg_add_one_eq p (k + 1)).symm)
      OrderHom.id (fun i ↦ ?_) y)
      (heq_of_eq (augMap_id K _ _))
    rw [residual_apply_val, joinCollapseOf_apply_val,
      joinCollapseVal_of_le p x
        (show j ≤ (i : ℕ) + cut (joinCollapseOf p hjk x) (p + 1) by omega)]
    show p + 1 + ((i : ℕ) + cut (joinCollapseOf p hjk x) (p + 1) - j) - (p + 1) = (i : ℕ)
    omega

/-! ### The collapse map of the front identity simplex -/

lemma joinCollapseVal_idAug (p i : ℕ) : joinCollapseVal p (idAug.{u} p) i = i := by
  by_cases h : i < p + 1
  · rw [joinCollapseVal_of_lt p (idAug.{u} p) h, augVal_idAug p h]
  · rw [joinCollapseVal_of_le p (idAug.{u} p) (by omega)]
    omega

/-- The collapse map of `id_{Δ[p]} ⋆ y` is the identity. -/
lemma mkHom_joinCollapseOf_idAug (p n : ℕ) :
    mkHom (joinCollapseOf p (k := n + 1) (Nat.add_succ (p + 1) n) (idAug.{u} p)) =
      𝟙 ⦋p + 1 + n⦌ :=
  Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ Fin.ext (joinCollapseVal_idAug p (i : ℕ))))

/-! ### The universal property -/

section UniversalProperty

variable {K X : SSet.{u}} {p : ℕ} {f : X _⦋p⦌}

/-- The extension of `g : K ⟶ X_{f/}` to the augmented simplicial set: on `K⁺ 0 = pt` it is
the base simplex `f`, on `K⁺ (k + 1) = K _⦋k⦌` it is `g` (with values in `X _⦋p + 1 + k⦌`). -/
def cosAug (g : K ⟶ (X.coslice f : SSet.{u})) : ∀ {k : ℕ}, K.aug k → X _⦋augDeg p k⦌
  | 0, _ => f
  | _ + 1, y => (g.app _ y).1

lemma cosAug_augMap (g : K ⟶ (X.coslice f : SSet.{u})) {a b : ℕ} (ρ : Fin a →o Fin b)
    (y : K.aug b) :
    cosAug g (K.augMap ρ y) = X.map (mkHom (pShift p ρ)).op (cosAug g y) := by
  cases a with
  | zero =>
    cases b with
    | zero =>
      change f = X.map (mkHom (OrderHom.id : Fin (p + 1) →o Fin (p + 1))).op f
      rw [show mkHom (OrderHom.id : Fin (p + 1) →o Fin (p + 1)) = 𝟙 _ from rfl, op_id,
        Functor.map_id_apply]
    | succ b =>
      change f = X.map (frontHom p b).op (g.app (op ⦋b⦌) y).1
      exact ((g.app (op ⦋b⦌) y).2).symm
  | succ a =>
    cases b with
    | zero => exact (ρ 0).elim0
    | succ b =>
      have h : ∀ y : K _⦋b⦌, ((g.app (op ⦋a⦌) (K.map (mkHom ρ).op y)).1 : X _⦋p + 1 + a⦌) =
          X.map (mkHom (shiftFun p (m := a) (n := b) ρ)).op (g.app (op ⦋b⦌) y).1 := fun y ↦ by
        rw [NatTrans.naturality_apply]
        rfl
      exact h y

/-- The morphism `Δ[p] ⋆ K ⟶ X` associated with `g : K ⟶ X_{f/}`, on simplices, in component
form (see `SSet.joinCollapseOf` for why the components rather than a simplex). -/
def toJoinFunOf (g : K ⟶ (X.coslice f : SSet.{u})) {q j k : ℕ} (hjk : j + k = q + 1)
    (x : (Δ[p] : SSet.{u}).aug j) (y : K.aug k) : X _⦋q⦌ :=
  X.map (mkHom (joinCollapseOf p hjk x)).op (cosAug g y)

lemma toJoinFunOf_map (g : K ⟶ (X.coslice f : SSet.{u})) {q q' j k : ℕ} (hjk : j + k = q + 1)
    (x : (Δ[p] : SSet.{u}).aug j) (y : K.aug k) (ρ : Fin (q' + 1) →o Fin (q + 1))
    (h' : cut ρ j + (q' + 1 - cut ρ j) = q' + 1) :
    toJoinFunOf g h' ((Δ[p] : SSet.{u}).augMap (initialSeg ρ j) x)
        (K.augMap (residual ρ j k hjk) y) = X.map (mkHom ρ).op (toJoinFunOf g hjk x y) := by
  dsimp only [toJoinFunOf]
  rw [cosAug_augMap, ← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp]
  exact congrArg (fun t : ⦋q'⦌ ⟶ ⦋augDeg p k⦌ ↦ X.map t.op (cosAug g y))
    (Hom.ext _ _ (OrderHom.ext _ _ (funext fun i ↦ Fin.ext (joinCollapseOf_map p hjk x ρ h' i))))

/-- The morphism `Δ[p] ⋆ K ⟶ X` associated with `g : K ⟶ X_{f/}`, on simplices. -/
def toJoinFun (g : K ⟶ (X.coslice f : SSet.{u})) {q : ℕ}
    (s : JoinSimplex (Δ[p] : SSet.{u}) K q) : X _⦋q⦌ :=
  toJoinFunOf g s.hjk s.x s.y

lemma toJoinFun_eq (g : K ⟶ (X.coslice f : SSet.{u})) {q : ℕ}
    (s : JoinSimplex (Δ[p] : SSet.{u}) K q) :
    toJoinFun g s = X.map (mkHom (joinCollapse p s)).op (cosAug g s.y) := rfl

lemma toJoinFun_map (g : K ⟶ (X.coslice f : SSet.{u})) {q q' : ℕ}
    (ρ : Fin (q' + 1) →o Fin (q + 1)) (s : JoinSimplex (Δ[p] : SSet.{u}) K q) :
    toJoinFun g (s.map ρ) = X.map (mkHom ρ).op (toJoinFun g s) :=
  toJoinFunOf_map g s.hjk s.x s.y ρ (s.map ρ).hjk

/-- The morphism `Δ[p] ⋆ K ⟶ X` associated with `g : K ⟶ X_{f/}`. -/
@[simps]
def toJoin (g : K ⟶ (X.coslice f : SSet.{u})) : join (Δ[p] : SSet.{u}) K ⟶ X where
  app _ := ↾fun s ↦ toJoinFun g s
  naturality _ _ ρ := ConcreteCategory.hom_ext _ _
    fun (s : JoinSimplex (Δ[p] : SSet.{u}) K _) ↦ toJoinFun_map g ρ.unop.toOrderHom s

lemma toJoinFun_inl (g : K ⟶ (X.coslice f : SSet.{u})) {q : ℕ} (x : (Δ[p] : SSet.{u}) _⦋q⦌) :
    toJoinFun g (JoinSimplex.inl (B := K) x) = X.map (stdSimplex.objEquiv x).op f := by
  show X.map (mkHom (joinCollapseOf p (k := 0) (Nat.add_zero (q + 1)) x)).op f = _
  rw [mkHom_joinCollapseOf_top x]
  rfl

lemma toJoinFun_inr (g : K ⟶ (X.coslice f : SSet.{u})) {q : ℕ} (y : K _⦋q⦌) :
    toJoinFun g (JoinSimplex.inr (A := (Δ[p] : SSet.{u})) y) =
      X.map (backHom p q).op (g.app (op ⦋q⦌) y).1 := by
  show X.map (mkHom (joinCollapseOf p (j := 0) (k := q + 1) (Nat.zero_add (q + 1))
    (PUnit.unit : (Δ[p] : SSet.{u}).aug 0))).op (g.app (op ⦋q⦌) y).1 = _
  rw [mkHom_joinCollapseOf_zero p q]
  rfl

/-- The front block of `toJoin g` is the classifying map of the base simplex `f`. -/
lemma joinInl_comp_toJoin (g : K ⟶ (X.coslice f : SSet.{u})) :
    joinInl (Δ[p] : SSet.{u}) K ≫ toJoin g = yonedaEquiv.symm f :=
  NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun x ↦ toJoinFun_inl g x)

/-- The back block of `toJoin g` is `g` followed by the projection `X_{f/} ⟶ X`. -/
lemma joinInr_comp_toJoin (g : K ⟶ (X.coslice f : SSet.{u})) :
    joinInr (Δ[p] : SSet.{u}) K ≫ toJoin g = g ≫ X.cosliceProj f :=
  NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun y ↦ toJoinFun_inr g y)

/-- The morphism `K ⟶ X_{f/}` associated with `F : Δ[p] ⋆ K ⟶ X` restricting to `f` on the
front block, on simplices. -/
def fromJoinFun (F : join (Δ[p] : SSet.{u}) K ⟶ X)
    (hF : joinInl (Δ[p] : SSet.{u}) K ≫ F = yonedaEquiv.symm f) {n : ℕ} (y : K _⦋n⦌) :
    (X.coslice f : SSet.{u}) _⦋n⦌ :=
  ⟨F.app (op ⦋p + 1 + n⦌) (joinCons p y), by
    show X.map (frontHom p n).op (F.app (op ⦋p + 1 + n⦌) (joinCons p y)) = f
    refine (NatTrans.naturality_apply F (frontHom p n).op
      (joinCons p y : (join (Δ[p] : SSet.{u}) K).obj (op ⦋p + 1 + n⦌))).symm.trans ?_
    show F.app (op ⦋p⦌) ((joinCons p y).map (castAddOrderHom p n)) = f
    rw [joinCons_map_castAddOrderHom]
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app hF (op ⦋p⦌)) (idAug.{u} p)
    change F.app (op ⦋p⦌) (JoinSimplex.inl (B := K) (idAug.{u} p)) =
      X.map (stdSimplex.objEquiv (idAug.{u} p : (Δ[p] : SSet.{u}) _⦋p⦌)).op f at h1
    rw [h1, objEquiv_idAug, op_id, Functor.map_id_apply]⟩

/-- The morphism `K ⟶ X_{f/}` associated with `F : Δ[p] ⋆ K ⟶ X` restricting to `f` on the
front block. -/
@[simps]
def fromJoin (F : join (Δ[p] : SSet.{u}) K ⟶ X)
    (hF : joinInl (Δ[p] : SSet.{u}) K ≫ F = yonedaEquiv.symm f) :
    K ⟶ (X.coslice f : SSet.{u}) where
  app n := ↾fun y ↦ fromJoinFun F hF y
  naturality n m α := ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext (by
    change F.app (op ⦋p + 1 + m.unop.len⦌) (joinCons p (K.map α y)) =
      X.map (shiftHom p α.unop).op (F.app (op ⦋p + 1 + n.unop.len⦌) (joinCons p y))
    refine Eq.trans ?_ (NatTrans.naturality_apply F (shiftHom p α.unop).op
      (joinCons p y : (join (Δ[p] : SSet.{u}) K).obj (op ⦋p + 1 + n.unop.len⦌)))
    show _ = F.app (op ⦋p + 1 + m.unop.len⦌) ((joinCons p y).map
      (shiftFun p (m := m.unop.len) (n := n.unop.len) α.unop.toOrderHom))
    rw [joinCons_map_shiftFun]
    rfl)

lemma toJoin_fromJoin (F : join (Δ[p] : SSet.{u}) K ⟶ X)
    (hF : joinInl (Δ[p] : SSet.{u}) K ≫ F = yonedaEquiv.symm f) : toJoin (fromJoin F hF) = F := by
  ext n s
  obtain ⟨j, k, hjk, x, y⟩ := s
  cases k with
  | zero =>
    obtain rfl : j = n.unop.len + 1 := by omega
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app hF n) x
    change F.app n (JoinSimplex.inl (B := K) x) =
      X.map (stdSimplex.objEquiv x).op f at h1
    show X.map (mkHom (joinCollapseOf p hjk x)).op f = _
    rw [mkHom_joinCollapseOf_top x]
    exact h1.symm
  | succ k =>
    show X.map (mkHom (joinCollapseOf p hjk x)).op
      (F.app (op ⦋p + 1 + k⦌) (joinCons p y)) = _
    refine (NatTrans.naturality_apply F (mkHom (joinCollapseOf p hjk x)).op
      (joinCons p y : (join (Δ[p] : SSet.{u}) K).obj (op ⦋p + 1 + k⦌))).symm.trans ?_
    show F.app n ((joinCons p y).map (joinCollapseOf p hjk x)) = _
    exact congrArg (fun t ↦ (ConcreteCategory.hom (F.app n)) t)
      (joinCons_map_joinCollapseOf p hjk x y)

lemma fromJoin_toJoin (g : K ⟶ (X.coslice f : SSet.{u})) :
    fromJoin (toJoin g) (joinInl_comp_toJoin g) = g := by
  ext n y
  refine Subtype.ext ?_
  show X.map (mkHom (joinCollapseOf p (k := n.unop.len + 1)
    (Nat.add_succ (p + 1) n.unop.len) (idAug.{u} p))).op (g.app n y).1 = (g.app n y).1
  refine Eq.trans (congrArg
    (fun t : ⦋p + 1 + n.unop.len⦌ ⟶ ⦋p + 1 + n.unop.len⦌ ↦ X.map t.op (g.app n y).1)
    (mkHom_joinCollapseOf_idAug p n.unop.len)) ?_
  rw [op_id, Functor.map_id_apply]

/-- (U1') The universal property of the join against the décalage model of the coslice
(Kerodon 0189): morphisms `K ⟶ X_{f/}` correspond to morphisms `Δ[p] ⋆ K ⟶ X` restricting to
`f` on the front block. Under this bijection `g ≫ X.cosliceProj f = joinInr ≫ ĝ`
(`joinInr_comp_toJoin`), and it is natural in `K` (`toJoin_naturality`). This generalises
`SSet.coneHomEquiv`, which is the case `p = 0`. -/
@[simps]
def cosliceHomEquiv (K X : SSet.{u}) {p : ℕ} (f : X _⦋p⦌) :
    (K ⟶ (X.coslice f : SSet.{u})) ≃
      {F : join (Δ[p] : SSet.{u}) K ⟶ X //
        joinInl (Δ[p] : SSet.{u}) K ≫ F = yonedaEquiv.symm f} where
  toFun g := ⟨toJoin g, joinInl_comp_toJoin g⟩
  invFun F := fromJoin F.1 F.2
  left_inv g := fromJoin_toJoin g
  right_inv F := Subtype.ext (toJoin_fromJoin F.1 F.2)

lemma cosAug_comp {L : SSet.{u}} (u : L ⟶ K) (g : K ⟶ (X.coslice f : SSet.{u})) {k : ℕ}
    (y : L.aug k) : cosAug (u ≫ g) y = cosAug g (augHom u y) := by
  cases k with
  | zero => rfl
  | succ k => rfl

lemma toJoin_naturality {L : SSet.{u}} (u : L ⟶ K) (g : K ⟶ (X.coslice f : SSet.{u})) :
    toJoin (u ≫ g) = joinMap (𝟙 (Δ[p] : SSet.{u})) u ≫ toJoin g := by
  ext n s
  show X.map (mkHom (joinCollapseOf p s.hjk s.x)).op (cosAug (u ≫ g) s.y) =
    X.map (mkHom (joinCollapseOf p s.hjk (augHom (𝟙 (Δ[p] : SSet.{u})) s.x))).op
      (cosAug g (augHom u s.y))
  rw [cosAug_comp, augHom_id]

end UniversalProperty

end SSet
