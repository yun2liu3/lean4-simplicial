/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import SimplicialHomotopy.Slice.Undercategory
import SimplicialHomotopy.Fibration.RightFibrations

/-!
# The cone `Δ[0] ⋆ K`

We define the cone `Δ[0] ⋆ K` of a simplicial set `K` (Kerodon Tag 0177) by the explicit
description of its simplices (Kerodon Tag 0170): an `n`-simplex is a pair `(j, k)` with
`j + k = n + 1` (`j` vertices at the cone point, `k` remaining vertices) together with a simplex
of the *augmented* simplicial set `K⁺` in degree `k`, where `K⁺ 0 = pt` and
`K⁺ (k + 1) = K _⦋k⦌`.

* `SSet.aug K k` : the augmented simplicial set (`K⁺`); `SSet.augMap` its action on monotone
  maps `Fin a →o Fin b` (with `Fin 0 = ∅`).
* `SSet.cut α j` : for `α : Fin (m + 1) →o Fin (n + 1)`, the number of `i` with `α i < j`;
  `SSet.lt_cut_iff` says `i < cut α j ↔ α i < j`.
* `SSet.residual α j k` : the restriction `Fin (m + 1 - cut α j) →o Fin k` of `α` to the
  vertices not sent to the cone point.
* `SSet.ConeSimplex K n`, `SSet.cone K`, `SSet.coneMap`, `SSet.coneFunctor`, `SSet.coneι`,
  `SSet.conePt`.
* (U1) `SSet.coneHomEquiv K X c : (K ⟶ X.under c) ≃ {f : cone K ⟶ X // conePt K ≫ f = const c}`,
  with `SSet.coneι_comp_toCone`, `SSet.conePt_comp_toCone`, naturality `SSet.toCone_naturality`
  (in `K`) and `SSet.toCone_naturality_right` (in `X`, via `SSet.underMap`).
  Note: `(K ⟶ X.dec) ≃ (cone K ⟶ X)` is false in general (`K = ∅`, or `K` disconnected).
* (C2) `SSet.Subcomplex.cone A`, `cone_sup`, `cone_inf`, `cone_top`, `range_coneMap_ι`,
  `mem_range_coneι_iff`, the monos `coneMap_mono`, `coneι_mono`, and the identification
  `coneToSub`/`coneLift` of `Δ[0] ⋆ A` with `Subcomplex.cone A`.
* (U2) `SSet.InnerAnodyneConeOfLeftAnodyne` (the statement of [Lur09, 2.1.2.3], proved in
  `Join/ConeLifting.lean`) and the derived
  `SSet.leftFibration_underProj_of_innerAnodyne_cone`
  ([Lur09, 2.1.2.2], taking that statement as a hypothesis).
* (C1) `SSet.stdSimplex.coneIso m : cone Δ[m] ≅ Δ[m + 1]` with `coneIso_hom_conePt`,
  `coneIso_hom_coneι`, `coneMap_map_coneIso_hom` (compatibility with `coneShiftHom`).
* (C3) `SSet.coneNerveIso V : cone (nerve V) ≅ nerve (WithBot V)` for a preorder `V`, with
  `conePt_coneNerveIso_hom`, `coneι_coneNerveIso_hom`, `coneNerveIso_hom_naturality`.
* (C4) `SSet.cone_horn_sup_range_coneι`, identifying `(Δ[0] ⋆ Λ[n + 1, i]) ∪ (∅ ⋆ Δ[n + 1])`
  with the horn `Λ[n + 2, i.succ]` under (C1), and the resulting case of (U2) for a left horn,
  `SSet.innerAnodyne_cone_horn`.
-/

universe u

open CategoryTheory Opposite Simplicial

namespace SSet

/-! ### The augmented simplicial set `K⁺` -/

/-- The augmented simplicial set: `K.aug 0 = pt`, `K.aug (k + 1) = K _⦋k⦌`. -/
def aug (K : SSet.{u}) : ℕ → Type u
  | 0 => PUnit
  | k + 1 => K _⦋k⦌

/-- The action of a monotone map `Fin a →o Fin b` on `K.aug`. -/
def augMap (K : SSet.{u}) : ∀ {a b : ℕ}, (Fin a →o Fin b) → K.aug b → K.aug a
  | 0, _, _, _ => PUnit.unit
  | _ + 1, 0, f, _ => (f 0).elim0
  | _ + 1, _ + 1, f, y => K.map (SimplexCategory.mkHom f).op y

lemma augMap_succ_succ (K : SSet.{u}) {a b : ℕ} (f : Fin (a + 1) →o Fin (b + 1))
    (y : K _⦋b⦌) : K.augMap f y = K.map (SimplexCategory.mkHom f).op y := rfl

lemma augMap_id (K : SSet.{u}) (a : ℕ) (y : K.aug a) :
    K.augMap (OrderHom.id : Fin a →o Fin a) y = y := by
  cases a with
  | zero => rfl
  | succ a =>
    have h : ∀ y : K _⦋a⦌,
        K.map (SimplexCategory.mkHom (OrderHom.id : Fin (a + 1) →o Fin (a + 1))).op y = y :=
      fun y ↦ by
        rw [show SimplexCategory.mkHom (OrderHom.id : Fin (a + 1) →o Fin (a + 1)) = 𝟙 _ from rfl,
          op_id, Functor.map_id_apply]
    exact h y

lemma augMap_comp (K : SSet.{u}) {a b c : ℕ} (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (y : K.aug c) : K.augMap (g.comp f) y = K.augMap f (K.augMap g y) := by
  cases a with
  | zero => rfl
  | succ a =>
    cases b with
    | zero => exact (f 0).elim0
    | succ b =>
      cases c with
      | zero => exact (g 0).elim0
      | succ c =>
        have h : ∀ y : K _⦋c⦌, K.map (SimplexCategory.mkHom (g.comp f)).op y =
            K.map (SimplexCategory.mkHom f).op (K.map (SimplexCategory.mkHom g).op y) :=
          fun y ↦ by
            rw [← Functor.map_comp_apply, ← op_comp]
            rfl
        exact h y

lemma augMap_congr (K : SSet.{u}) {a a' b : ℕ} (ha : a = a') (f : Fin a →o Fin b)
    (f' : Fin a' →o Fin b) (hf : ∀ i : Fin a, (f i : ℕ) = f' (Fin.cast ha i)) (y : K.aug b) :
    HEq (K.augMap f y) (K.augMap f' y) := by
  subst ha
  have : f = f' := OrderHom.ext _ _ (funext fun i ↦ Fin.ext (hf i))
  subst this
  rfl

/-! ### The cut of a monotone map -/

/-- The number of `i` with `α i < j`: the vertices sent to the cone point. -/
def cut {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin (m + 1) ↦ (α i : ℕ) < j).card

lemma cut_le {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (j : ℕ) : cut α j ≤ m + 1 :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- The key property of the cut: `{i | α i < j}` is the initial segment of length `cut α j`. -/
lemma lt_cut_iff {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (j : ℕ) (i : Fin (m + 1)) :
    (i : ℕ) < cut α j ↔ (α i : ℕ) < j := by
  constructor
  · intro h
    by_contra h'
    have hsub : (Finset.univ.filter fun l : Fin (m + 1) ↦ (α l : ℕ) < j) ⊆ Finset.Iio i := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [Finset.mem_Iio]
      by_contra hli
      have := α.monotone (not_lt.1 hli)
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    exact absurd h (not_lt.2 this)
  · intro h
    have hsub : Finset.Iic i ⊆ (Finset.univ.filter fun l : Fin (m + 1) ↦ (α l : ℕ) < j) := by
      intro l hl
      simp only [Finset.mem_Iic] at hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := α.monotone hl
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    exact this

lemma _root_.Nat.eq_of_forall_fin_lt_iff {m j j' : ℕ} (hj : j ≤ m + 1) (hj' : j' ≤ m + 1)
    (h : ∀ i : Fin (m + 1), (i : ℕ) < j ↔ (i : ℕ) < j') : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact lt_irrefl j ((h ⟨j, by omega⟩).2 hlt)
  · exact lt_irrefl j' ((h ⟨j', by omega⟩).1 hlt)

lemma cut_id {m : ℕ} (j : ℕ) (hj : j ≤ m + 1) :
    cut (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) j = j :=
  Nat.eq_of_forall_fin_lt_iff (cut_le _ _) hj fun i ↦ lt_cut_iff _ _ i

lemma cut_comp {l m n : ℕ} (α : Fin (l + 1) →o Fin (m + 1)) (β : Fin (m + 1) →o Fin (n + 1))
    (j : ℕ) : cut (β.comp α) j = cut α (cut β j) :=
  Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (cut_le _ _) fun i ↦ by
    rw [lt_cut_iff, lt_cut_iff, lt_cut_iff]
    rfl

/-- The residual map: the restriction of `α` to the vertices not sent to the cone point,
`i ↦ α (i + cut α j) - j`, where `j + k = n + 1`. -/
def residual {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (j k : ℕ) (hjk : j + k = n + 1) :
    Fin (m + 1 - cut α j) →o Fin k where
  toFun i := ⟨(α ⟨i + cut α j, by omega⟩ : ℕ) - j, by
    have h1 := (lt_cut_iff α j ⟨i + cut α j, by omega⟩).not
    have h2 := (α ⟨i + cut α j, by omega⟩).isLt
    simp only [not_lt] at h1
    omega⟩
  monotone' i i' hii' := by
    have := α.monotone (show (⟨i + cut α j, by omega⟩ : Fin (m + 1)) ≤ ⟨i' + cut α j, by omega⟩
      from Fin.mk_le_mk.2 (by omega))
    simp only [Fin.mk_le_mk]
    omega

lemma residual_apply_val {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (j k : ℕ)
    (hjk : j + k = n + 1) (i : Fin (m + 1 - cut α j)) :
    (residual α j k hjk i : ℕ) = (α ⟨i + cut α j, by have := i.isLt; omega⟩ : ℕ) - j := rfl

/-- `j ≤ α (i + cut α j)`. -/
lemma le_apply_add_cut {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (j : ℕ) (i : ℕ)
    (hi : i + cut α j < m + 1) : j ≤ α ⟨i + cut α j, hi⟩ := by
  have h1 := (lt_cut_iff α j ⟨i + cut α j, hi⟩).not
  simp only [not_lt] at h1
  exact h1.1 (by omega)

lemma residual_comp_val {l m n : ℕ} (α : Fin (l + 1) →o Fin (m + 1))
    (β : Fin (m + 1) →o Fin (n + 1)) (j k : ℕ) (hjk : j + k = n + 1)
    (i : Fin (l + 1 - cut (β.comp α) j)) (i' : Fin (l + 1 - cut α (cut β j)))
    (hi : (i : ℕ) = i') :
    (residual (β.comp α) j k hjk i : ℕ) =
      residual β j k hjk (residual α (cut β j) (m + 1 - cut β j)
        (by have := cut_le β j; omega) i') := by
  rw [residual_apply_val, residual_apply_val]
  have hc := cut_comp α β j
  have h1 := le_apply_add_cut α (cut β j) i' (by have := i'.isLt; omega)
  have h4 : (α ⟨i + cut (β.comp α) j, by have := i.isLt; omega⟩ : ℕ) =
      α ⟨i' + cut α (cut β j), by have := i'.isLt; omega⟩ :=
    congrArg (fun t : Fin (l + 1) ↦ (α t : ℕ)) (Fin.ext (by simp [hc, hi]))
  have key : ∀ a b : Fin (m + 1), (a : ℕ) = b → (β a : ℕ) - j = (β b : ℕ) - j :=
    fun a b h ↦ by rw [Fin.ext h]
  refine key _ _ ?_
  dsimp only
  rw [residual_apply_val]
  omega

lemma cut_zero {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) : cut α 0 = 0 :=
  Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (by omega) fun i ↦ by
    rw [lt_cut_iff]; omega

lemma cut_top {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) : cut α (n + 1) = m + 1 :=
  Nat.eq_of_forall_fin_lt_iff (cut_le _ _) le_rfl fun i ↦ by
    rw [lt_cut_iff]; exact ⟨fun _ ↦ i.isLt, fun _ ↦ (α i).isLt⟩

/-- The residual of `α` at the cut `0` is `α` itself. -/
lemma residual_zero_val {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (k : ℕ) (hk : 0 + k = n + 1)
    (i : Fin (m + 1 - cut α 0)) (i' : Fin (m + 1)) (hi : (i : ℕ) = i') :
    (residual α 0 k hk i : ℕ) = α i' := by
  rw [residual_apply_val, Nat.sub_zero]
  exact congrArg (fun t : Fin (m + 1) ↦ (α t : ℕ)) (Fin.ext (by simp [cut_zero, hi]))

/-! ### The action of morphisms on `K⁺` -/

/-- The action of a morphism `K ⟶ L` on the augmented simplicial sets. -/
def augHom {K L : SSet.{u}} (f : K ⟶ L) : ∀ {k : ℕ}, K.aug k → L.aug k
  | 0, _ => PUnit.unit
  | _ + 1, y => f.app _ y

lemma augHom_augMap {K L : SSet.{u}} (f : K ⟶ L) {a b : ℕ} (ρ : Fin a →o Fin b)
    (y : K.aug b) : augHom f (K.augMap ρ y) = L.augMap ρ (augHom f y) := by
  cases a with
  | zero => rfl
  | succ a =>
    cases b with
    | zero => exact (ρ 0).elim0
    | succ b =>
      have h : ∀ y : K _⦋b⦌, f.app _ (K.map (SimplexCategory.mkHom ρ).op y) =
          L.map (SimplexCategory.mkHom ρ).op (f.app _ y) :=
        fun y ↦ NatTrans.naturality_apply f _ y
      exact h y

lemma augHom_id {K : SSet.{u}} {k : ℕ} (y : K.aug k) : augHom (𝟙 K) y = y := by
  cases k <;> rfl

lemma augHom_comp {K L M : SSet.{u}} (f : K ⟶ L) (g : L ⟶ M) {k : ℕ} (y : K.aug k) :
    augHom (f ≫ g) y = augHom g (augHom f y) := by
  cases k <;> rfl

/-! ### Simplices of the cone -/

/-- An `n`-simplex of `Δ[0] ⋆ K`: `j` vertices at the cone point, then a simplex of `K⁺`
of degree `k`, with `j + k = n + 1`. The cone point simplex is `k = 0`, and the simplices of
`K` itself are those with `j = 0`. -/
structure ConeSimplex (K : SSet.{u}) (n : ℕ) : Type u where
  /-- the number of vertices at the cone point -/
  j : ℕ
  /-- the number of remaining vertices -/
  k : ℕ
  hjk : j + k = n + 1
  /-- the simplex of `K⁺` on the remaining vertices -/
  y : K.aug k

namespace ConeSimplex

variable {K : SSet.{u}}

lemma ext_of_j_eq {n : ℕ} {x x' : K.ConeSimplex n} (hj : x.j = x'.j) (hy : HEq x.y x'.y) :
    x = x' := by
  obtain ⟨j, k, hjk, y⟩ := x
  obtain ⟨j', k', hjk', y'⟩ := x'
  dsimp only at hj hy
  subst hj
  obtain rfl : k = k' := by omega
  rw [eq_of_heq hy]

/-- The action of a simplicial operator. -/
def map {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (x : K.ConeSimplex n) : K.ConeSimplex m where
  j := cut α x.j
  k := m + 1 - cut α x.j
  hjk := by have := cut_le α x.j; omega
  y := K.augMap (residual α x.j x.k x.hjk) x.y

@[simp] lemma map_j {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (x : K.ConeSimplex n) :
    (x.map α).j = cut α x.j := rfl

@[simp] lemma map_k {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (x : K.ConeSimplex n) :
    (x.map α).k = m + 1 - cut α x.j := rfl

lemma map_id {n : ℕ} (x : K.ConeSimplex n) : x.map OrderHom.id = x := by
  have hj : x.j ≤ n + 1 := by have := x.hjk; omega
  refine ext_of_j_eq (cut_id x.j hj) ?_
  refine HEq.trans (augMap_congr K (a' := x.k) (by rw [cut_id x.j hj]; have := x.hjk; omega)
    (residual OrderHom.id x.j x.k x.hjk) OrderHom.id (fun i ↦ ?_) x.y)
    (heq_of_eq (augMap_id K _ _))
  rw [residual_apply_val]
  show ((⟨i + cut OrderHom.id x.j, _⟩ : Fin (n + 1)) : ℕ) - x.j = (i : ℕ)
  dsimp only
  have := cut_id x.j hj
  omega

lemma map_comp {l m n : ℕ} (α : Fin (l + 1) →o Fin (m + 1)) (β : Fin (m + 1) →o Fin (n + 1))
    (x : K.ConeSimplex n) : x.map (β.comp α) = (x.map β).map α := by
  refine ext_of_j_eq (cut_comp α β x.j) ?_
  show HEq (K.augMap (residual (β.comp α) x.j x.k x.hjk) x.y)
    (K.augMap (residual α (cut β x.j) (m + 1 - cut β x.j) (x.map β).hjk)
      (K.augMap (residual β x.j x.k x.hjk) x.y))
  rw [← augMap_comp]
  exact augMap_congr K (by rw [cut_comp]) _ _
    (fun i ↦ residual_comp_val α β x.j x.k x.hjk i _ rfl) x.y

/-- The image of a simplex under a morphism `K ⟶ L`. -/
def mapHom {L : SSet.{u}} (f : K ⟶ L) {n : ℕ} (x : K.ConeSimplex n) : L.ConeSimplex n :=
  ⟨x.j, x.k, x.hjk, augHom f x.y⟩

lemma mapHom_map {L : SSet.{u}} (f : K ⟶ L) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (x : K.ConeSimplex n) : (x.map α).mapHom f = (x.mapHom f).map α :=
  ext_of_j_eq rfl (heq_of_eq (augHom_augMap f _ _))

lemma mapHom_id {n : ℕ} (x : K.ConeSimplex n) : x.mapHom (𝟙 K) = x :=
  ext_of_j_eq rfl (heq_of_eq (augHom_id _))

lemma mapHom_comp {L M : SSet.{u}} (f : K ⟶ L) (g : L ⟶ M) {n : ℕ} (x : K.ConeSimplex n) :
    x.mapHom (f ≫ g) = (x.mapHom f).mapHom g :=
  ext_of_j_eq rfl (heq_of_eq (augHom_comp f g _))

/-- The cone point simplex (all vertices at the cone point). -/
def pt (K : SSet.{u}) (n : ℕ) : K.ConeSimplex n := ⟨n + 1, 0, rfl, PUnit.unit⟩

/-- The simplex of the cone underlying a simplex of `K` (no vertex at the cone point). -/
def ofSimplex {n : ℕ} (y : K _⦋n⦌) : K.ConeSimplex n := ⟨0, n + 1, Nat.zero_add _, y⟩

lemma pt_map {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) : (pt K n).map α = pt K m := by
  refine ext_of_j_eq (cut_top _) ?_
  have hc := cut_top α
  refine HEq.trans (augMap_congr K (a' := 0)
    (by change m + 1 - cut α (n + 1) = 0; omega) _ OrderHom.id
    (fun i ↦ absurd i.isLt (by change ¬ ((i : ℕ) < m + 1 - cut α (n + 1)); omega))
    PUnit.unit) ?_
  exact heq_of_eq rfl

lemma ofSimplex_map {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (y : K _⦋n⦌) :
    (ofSimplex y).map α = ofSimplex (K.map (SimplexCategory.mkHom α).op y) := by
  refine ext_of_j_eq (cut_zero _) ?_
  refine HEq.trans (augMap_congr K (a' := m + 1) (by rw [cut_zero]; rfl) _ α
    (fun i ↦ residual_zero_val _ _ _ i _ rfl) y) ?_
  exact heq_of_eq rfl

lemma pt_mapHom {L : SSet.{u}} (f : K ⟶ L) (n : ℕ) : (pt K n).mapHom f = pt L n := rfl

lemma ofSimplex_mapHom {L : SSet.{u}} (f : K ⟶ L) {n : ℕ} (y : K _⦋n⦌) :
    (ofSimplex y).mapHom f = ofSimplex (f.app _ y) := rfl

end ConeSimplex

/-- The cone `Δ[0] ⋆ K` (Kerodon 0177). -/
def cone (K : SSet.{u}) : SSet.{u} where
  obj n := K.ConeSimplex n.unop.len
  map α := ↾fun x ↦ x.map α.unop.toOrderHom
  map_id _ := ConcreteCategory.hom_ext _ _ fun x ↦ ConeSimplex.map_id x
  map_comp _ _ := ConcreteCategory.hom_ext _ _ fun x ↦ ConeSimplex.map_comp _ _ x

@[simp]
lemma cone_map_apply (K : SSet.{u}) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) (x : K.cone.obj m) :
    K.cone.map α x = x.map α.unop.toOrderHom := rfl

/-- The cone of a morphism. -/
@[simps]
def coneMap {K L : SSet.{u}} (f : K ⟶ L) : cone K ⟶ cone L where
  app _ := ↾fun x ↦ x.mapHom f
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun x ↦ ConeSimplex.mapHom_map f _ x

@[simp]
lemma coneMap_id (K : SSet.{u}) : coneMap (𝟙 K) = 𝟙 (cone K) := by
  ext _ x
  exact ConeSimplex.mapHom_id x

@[simp]
lemma coneMap_comp {K L M : SSet.{u}} (f : K ⟶ L) (g : L ⟶ M) :
    coneMap (f ≫ g) = coneMap f ≫ coneMap g := by
  ext _ x
  exact ConeSimplex.mapHom_comp f g x

/-- The cone functor `Δ[0] ⋆ (−) : SSet ⥤ SSet`. -/
@[simps]
def coneFunctor : SSet.{u} ⥤ SSet.{u} where
  obj := cone
  map := coneMap

/-- The inclusion `K = ∅ ⋆ K ⟶ Δ[0] ⋆ K`: the simplices with `j = 0`. -/
@[simps]
def coneι (K : SSet.{u}) : K ⟶ cone K where
  app _ := ↾fun y ↦ ConeSimplex.ofSimplex y
  naturality _ _ α := ConcreteCategory.hom_ext _ _ fun y ↦
    (ConeSimplex.ofSimplex_map α.unop.toOrderHom y).symm

/-- The cone point `Δ[0] = Δ[0] ⋆ ∅ ⟶ Δ[0] ⋆ K`: the simplices with `k = 0`. -/
@[simps]
def conePt (K : SSet.{u}) : Δ[0] ⟶ cone K where
  app n := ↾fun _ ↦ ConeSimplex.pt K n.unop.len
  naturality _ _ α := ConcreteCategory.hom_ext _ _ fun _ ↦
    (ConeSimplex.pt_map α.unop.toOrderHom).symm

lemma coneι_naturality {K L : SSet.{u}} (f : K ⟶ L) : f ≫ coneι L = coneι K ≫ coneMap f := rfl

lemma conePt_naturality {K L : SSet.{u}} (f : K ⟶ L) : conePt K ≫ coneMap f = conePt L := rfl

/-! ### The universal property against the décalage

A morphism `Δ[0] ⋆ K ⟶ X` sending the cone point to `c` is the same as a morphism
`K ⟶ X_{c/}` (décalage model). Note that `(K ⟶ X.dec) ≃ (cone K ⟶ X)` is *false* in general
(`K = ∅`, or `K` disconnected), so the universal property is stated with the cone point fixed.
-/

/-- The map `Fin (n + 1) →o Fin (k + 1)`, `i ↦ i + 1 - j`, collapsing the first `j` vertices to
`0` and shifting the remaining `k` vertices to `1, …, k`, where `j + k = n + 1`. -/
def collapse {n : ℕ} (j k : ℕ) (hjk : j + k = n + 1) : Fin (n + 1) →o Fin (k + 1) where
  toFun i := ⟨i + 1 - j, by have := i.isLt; omega⟩
  monotone' i i' h := by
    simp only [Fin.mk_le_mk]
    omega

lemma collapse_apply_val {n : ℕ} (j k : ℕ) (hjk : j + k = n + 1) (i : Fin (n + 1)) :
    (collapse j k hjk i : ℕ) = i + 1 - j := rfl

/-- `SSet.augShift` (`Slice/Undercategory.lean`) at two successor degrees is
`SimplexCategory.coneShiftFun`, by definition of the latter. -/
lemma augShift_eq_coneShiftFun {m n : ℕ} (ρ : Fin (m + 1) →o Fin (n + 1)) :
    augShift ρ = SimplexCategory.coneShiftFun ρ := rfl

lemma augShift_val_of_eq_zero {a b : ℕ} (ρ : Fin a →o Fin b) (t : Fin (a + 1))
    (ht : (t : ℕ) = 0) : (augShift ρ t : ℕ) = 0 := by
  induction t using Fin.cases with
  | zero => rfl
  | succ s => simp at ht

lemma augShift_val_of_eq_succ {a b : ℕ} (ρ : Fin a →o Fin b) (t : Fin (a + 1)) (s : Fin a)
    (ht : (t : ℕ) = s + 1) : (augShift ρ t : ℕ) = ρ s + 1 := by
  induction t using Fin.cases with
  | zero => simp at ht
  | succ s' =>
    obtain rfl : s' = s := Fin.ext (by simpa using ht)
    simp

/-- The key identity: `augShift (residual α j k) ∘ collapse (cut α j) = collapse j k ∘ α`. -/
lemma augShift_residual_comp_collapse {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (j k : ℕ)
    (hjk : j + k = n + 1) (h' : cut α j + (m + 1 - cut α j) = m + 1) :
    (augShift (residual α j k hjk)).comp (collapse (cut α j) (m + 1 - cut α j) h') =
      (collapse j k hjk).comp α := by
  refine OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_)
  simp only [OrderHom.comp_coe, Function.comp_apply, collapse_apply_val]
  by_cases hi : (i : ℕ) < cut α j
  · have h1 := (lt_cut_iff α j i).1 hi
    rw [augShift_val_of_eq_zero _ _ (by rw [collapse_apply_val]; omega)]
    omega
  · have h1 := (lt_cut_iff α j i).not.1 hi
    have hi' : i - cut α j < m + 1 - cut α j := by have := i.isLt; omega
    rw [augShift_val_of_eq_succ _ _ ⟨i - cut α j, hi'⟩ (by rw [collapse_apply_val]; simp; omega),
      residual_apply_val]
    have h2 : (⟨(⟨i - cut α j, hi'⟩ : Fin (m + 1 - cut α j)) + cut α j, by omega⟩ : Fin (m + 1))
        = i := Fin.ext (by simp; omega)
    rw [h2]
    omega

section UniversalProperty

variable {K X : SSet.{u}} {c : X _⦋0⦌}

/-- The extension of `g : K ⟶ X_{c/}` to the augmented simplicial set: on `K⁺ 0 = pt` it is
the cone point `c`, on `K⁺ (k + 1) = K _⦋k⦌` it is `g` (with values in `X _⦋k + 1⦌`). -/
def decAug (g : K ⟶ (X.under c : SSet.{u})) : ∀ {k : ℕ}, K.aug k → X _⦋k⦌
  | 0, _ => c
  | _ + 1, y => (g.app _ y).1

lemma decAug_augMap (g : K ⟶ (X.under c : SSet.{u})) {a b : ℕ} (ρ : Fin a →o Fin b)
    (y : K.aug b) :
    decAug g (K.augMap ρ y) = X.map (SimplexCategory.mkHom (augShift ρ)).op (decAug g y) := by
  cases a with
  | zero =>
    cases b with
    | zero =>
      change c = X.map (SimplexCategory.mkHom (augShift ρ)).op c
      rw [SimplexCategory.Hom.ext_zero_left (SimplexCategory.mkHom (augShift ρ)) (𝟙 _), op_id,
        Functor.map_id_apply]
    | succ b =>
      change c = X.map (SimplexCategory.mkHom (augShift ρ)).op (g.app _ y).1
      rw [SimplexCategory.Hom.ext_zero_left (SimplexCategory.mkHom (augShift ρ))
        (SimplexCategory.const ⦋0⦌ ⦋b + 1⦌ 0)]
      exact ((g.app (op ⦋b⦌) y).2).symm
  | succ a =>
    cases b with
    | zero => exact (ρ 0).elim0
    | succ b =>
      have h : ∀ y : K _⦋b⦌, (g.app _ (K.map (SimplexCategory.mkHom ρ).op y)).1 =
          X.map (SimplexCategory.mkHom (augShift ρ)).op (g.app _ y).1 := fun y ↦ by
        rw [NatTrans.naturality_apply]
        rfl
      exact h y

/-- The morphism `Δ[0] ⋆ K ⟶ X` associated with `g : K ⟶ X_{c/}`, on simplices. -/
def toConeFun (g : K ⟶ (X.under c : SSet.{u})) {n : ℕ} (x : K.ConeSimplex n) : X _⦋n⦌ :=
  X.map (SimplexCategory.mkHom (collapse x.j x.k x.hjk)).op (decAug g x.y)

lemma toConeFun_map (g : K ⟶ (X.under c : SSet.{u})) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (x : K.ConeSimplex n) :
    toConeFun g (x.map α) = X.map (SimplexCategory.mkHom α).op (toConeFun g x) := by
  dsimp only [toConeFun]
  rw [← Functor.map_comp_apply, ← op_comp]
  show X.map (SimplexCategory.mkHom (collapse (cut α x.j) (m + 1 - cut α x.j) (x.map α).hjk)).op
    (decAug g (K.augMap (residual α x.j x.k x.hjk) x.y)) = _
  rw [decAug_augMap, ← Functor.map_comp_apply, ← op_comp]
  have key : SimplexCategory.mkHom (collapse (cut α x.j) (m + 1 - cut α x.j) (x.map α).hjk) ≫
      SimplexCategory.mkHom (augShift (residual α x.j x.k x.hjk)) =
      SimplexCategory.mkHom α ≫ SimplexCategory.mkHom (collapse x.j x.k x.hjk) :=
    SimplexCategory.Hom.ext _ _ (augShift_residual_comp_collapse α x.j x.k x.hjk (x.map α).hjk)
  rw [key]

/-- The morphism `Δ[0] ⋆ K ⟶ X` associated with `g : K ⟶ X_{c/}`. -/
@[simps]
def toCone (g : K ⟶ (X.under c : SSet.{u})) : cone K ⟶ X where
  app _ := ↾fun x ↦ toConeFun g x
  naturality _ _ α := ConcreteCategory.hom_ext _ _ fun x ↦ toConeFun_map g α.unop.toOrderHom x

lemma conePt_comp_toCone (g : K ⟶ (X.under c : SSet.{u})) : conePt K ≫ toCone g = const c := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  change X.map (SimplexCategory.mkHom (collapse (n.unop.len + 1) 0 rfl)).op c =
    X.map (n.unop.const ⦋0⦌ 0).op c
  have e : SimplexCategory.mkHom (collapse (n.unop.len + 1) 0 rfl) = n.unop.const ⦋0⦌ 0 := by
    ext i : 3
    exact Subsingleton.elim (α := Fin 1) _ _
  rw [e]

lemma coneι_comp_toCone (g : K ⟶ (X.under c : SSet.{u})) :
    coneι K ≫ toCone g = g ≫ X.underProj c := by
  ext n y
  change X.map (SimplexCategory.mkHom (collapse 0 (n.unop.len + 1) (Nat.zero_add _))).op
    (g.app n y).1 = X.map (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op (g.app n y).1
  congr 3

lemma toCone_naturality {L : SSet.{u}} (u : L ⟶ K) (g : K ⟶ (X.under c : SSet.{u})) :
    toCone (u ≫ g) = coneMap u ≫ toCone g := by
  ext n x
  obtain ⟨j, k, hjk, y⟩ := x
  cases k <;> rfl

/-- The unique monotone map `Fin 0 →o Fin b`. -/
def emptyOrderHom (b : ℕ) : Fin 0 →o Fin b := ⟨Fin.elim0, fun i ↦ i.elim0⟩

/-- Every monotone map out of `Fin 0` is `emptyOrderHom`. -/
lemma orderHom_fin_zero_eq {b : ℕ} (f : Fin 0 →o Fin b) : f = emptyOrderHom b :=
  OrderHom.ext _ _ (funext fun i ↦ i.elim0)

/-- The simplex `c ⋆ y` of the cone: the cone point followed by `y`. -/
def ConeSimplex.cons {n : ℕ} (y : K _⦋n⦌) : K.ConeSimplex (n + 1) :=
  ⟨1, n + 1, by omega, y⟩

lemma ConeSimplex.cons_map_coneShiftFun {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (y : K _⦋n⦌) :
    (ConeSimplex.cons y).map (SimplexCategory.coneShiftFun α) =
      ConeSimplex.cons (K.map (SimplexCategory.mkHom α).op y) := by
  have hc : cut (SimplexCategory.coneShiftFun α) 1 = 1 :=
    Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (by omega) fun i ↦ by
      rw [lt_cut_iff]
      induction i using Fin.cases with
      | zero => simp
      | succ i => simp
  refine ConeSimplex.ext_of_j_eq hc ?_
  refine HEq.trans (augMap_congr K (a' := m + 1) (by omega)
    (residual (SimplexCategory.coneShiftFun α) 1 (n + 1) (by omega)) α (fun i ↦ ?_) y) ?_
  · rw [residual_apply_val]
    have hi : (i : ℕ) < m + 1 := by have := i.isLt; omega
    have h2 : (⟨i + cut (SimplexCategory.coneShiftFun α) 1, by omega⟩ : Fin (m + 2)) =
        (⟨i, hi⟩ : Fin (m + 1)).succ := Fin.ext (by simp [hc])
    rw [h2, SimplexCategory.coneShiftFun_succ]
    simp only [Fin.val_succ, Nat.add_sub_cancel]
    rfl
  · exact heq_of_eq rfl

lemma ConeSimplex.cons_map_const {n : ℕ} (y : K _⦋n⦌) :
    (ConeSimplex.cons y).map ((SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).toOrderHom) =
      ConeSimplex.pt K 0 := by
  have hc : cut ((SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).toOrderHom) 1 = 1 :=
    Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (by omega) fun i ↦ by
      rw [lt_cut_iff]
      exact ⟨fun _ ↦ i.isLt, fun _ ↦ Nat.zero_lt_one⟩
  refine ConeSimplex.ext_of_j_eq hc ?_
  refine HEq.trans (augMap_congr K (a' := 0) (by change 0 + 1 - cut _ 1 = 0; omega)
    (residual (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).toOrderHom 1 (n + 1)
      (by change 1 + (n + 1) = n + 1 + 1; omega))
    (emptyOrderHom (n + 1))
    (fun i ↦ absurd i.isLt (by change ¬ ((i : ℕ) < 0 + 1 - cut _ 1); omega)) y) ?_
  exact heq_of_eq rfl

lemma const_app_zero_apply {Y : SSet.{u}} (c : X _⦋0⦌) (t : Y _⦋0⦌) :
    (const c : Y ⟶ X).app (op ⦋0⦌) t = c := by
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op c = c
  rw [SimplexCategory.Hom.ext_zero_left (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (𝟙 _), op_id,
    Functor.map_id_apply]

/-- The morphism `K ⟶ X_{c/}` associated with `f : Δ[0] ⋆ K ⟶ X` sending the cone point
to `c`, on simplices. -/
def fromConeFun (f : cone K ⟶ X) (hf : conePt K ≫ f = const c) {n : ℕ} (y : K _⦋n⦌) :
    (X.under c : SSet.{u}) _⦋n⦌ :=
  ⟨f.app (op ⦋n + 1⦌) (ConeSimplex.cons y), by
    change X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (f.app (op ⦋n + 1⦌) (.cons y)) = c
    refine (NatTrans.naturality_apply f (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (ConeSimplex.cons y : (cone K).obj (op ⦋n + 1⦌))).symm.trans ?_
    change f.app (op ⦋0⦌) ((ConeSimplex.cons y).map
      (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).toOrderHom) = c
    rw [ConeSimplex.cons_map_const]
    have := ConcreteCategory.congr_hom (NatTrans.congr_app hf (op ⦋0⦌)) (stdSimplex.const 0 0 _)
    change f.app (op ⦋0⦌) (ConeSimplex.pt K 0) =
      (const c : Δ[0] ⟶ X).app (op ⦋0⦌) (stdSimplex.const 0 0 _) at this
    rw [this, const_app_zero_apply]⟩

/-- The morphism `K ⟶ X_{c/}` associated with `f : Δ[0] ⋆ K ⟶ X` sending the cone point
to `c`. -/
@[simps]
def fromCone (f : cone K ⟶ X) (hf : conePt K ≫ f = const c) : K ⟶ (X.under c : SSet.{u}) where
  app n := ↾fun y ↦ fromConeFun f hf y
  naturality n m α := ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext (by
    change f.app (op ⦋m.unop.len + 1⦌) (ConeSimplex.cons (K.map α y)) =
      X.map (SimplexCategory.coneShiftHom α.unop).op
        (f.app (op ⦋n.unop.len + 1⦌) (ConeSimplex.cons y))
    refine Eq.trans ?_ (NatTrans.naturality_apply f (SimplexCategory.coneShiftHom α.unop).op
      (ConeSimplex.cons y : (cone K).obj (op ⦋n.unop.len + 1⦌)))
    change _ = f.app (op ⦋m.unop.len + 1⦌)
      ((ConeSimplex.cons y).map (SimplexCategory.coneShiftFun α.unop.toOrderHom))
    rw [ConeSimplex.cons_map_coneShiftFun]
    rfl)

lemma toCone_fromCone (f : cone K ⟶ X) (hf : conePt K ≫ f = const c) :
    toCone (fromCone f hf) = f := by
  ext n x
  obtain ⟨j, k, hjk, y⟩ := x
  cases k with
  | zero =>
    obtain rfl : j = n.unop.len + 1 := by omega
    change X.map (SimplexCategory.mkHom (collapse (n.unop.len + 1) 0 hjk)).op c =
      f.app n (ConeSimplex.pt K n.unop.len)
    have := ConcreteCategory.congr_hom (NatTrans.congr_app hf n) (stdSimplex.const 0 0 n)
    change f.app n (ConeSimplex.pt K n.unop.len) = X.map (n.unop.const ⦋0⦌ 0).op c at this
    rw [this]
    have e : SimplexCategory.mkHom (collapse (n.unop.len + 1) 0 hjk) = n.unop.const ⦋0⦌ 0 := by
      ext i : 3
      exact Subsingleton.elim (α := Fin 1) _ _
    rw [e]
  | succ k =>
    change X.map (SimplexCategory.mkHom (collapse j (k + 1) hjk)).op
      (f.app (op ⦋k + 1⦌) (ConeSimplex.cons y)) = f.app n ⟨j, k + 1, hjk, y⟩
    refine (NatTrans.naturality_apply f (SimplexCategory.mkHom (collapse j (k + 1) hjk)).op
      (ConeSimplex.cons y : (cone K).obj (op ⦋k + 1⦌))).symm.trans ?_
    change f.app n ((ConeSimplex.cons y).map (collapse j (k + 1) hjk)) = f.app n ⟨j, k + 1, hjk, y⟩
    congr 1
    have hc : cut (collapse j (k + 1) hjk) 1 = j :=
      Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (by omega) fun i ↦ by
        rw [lt_cut_iff, collapse_apply_val]; omega
    refine ConeSimplex.ext_of_j_eq hc ?_
    refine HEq.trans (augMap_congr K (a' := k + 1)
      (by omega)
      (residual (collapse j (k + 1) hjk) 1 (k + 1) (by omega)) OrderHom.id (fun i ↦ ?_) y)
      (heq_of_eq (augMap_id K _ _))
    rw [residual_apply_val, collapse_apply_val]
    change (i : ℕ) + cut (collapse j (k + 1) hjk) 1 + 1 - j - 1 = (i : ℕ)
    omega

lemma fromCone_toCone (g : K ⟶ (X.under c : SSet.{u})) :
    fromCone (toCone g) (conePt_comp_toCone g) = g := by
  ext n y
  refine Subtype.ext ?_
  change X.map (SimplexCategory.mkHom (collapse 1 (n.unop.len + 1) _)).op (g.app n y).1 =
    (g.app n y).1
  rw [show SimplexCategory.mkHom (collapse 1 (n.unop.len + 1) (by omega)) = 𝟙 _ from by
    ext i : 3
    exact Fin.ext (by change (i : ℕ) + 1 - 1 = (i : ℕ); omega)]
  rw [op_id, Functor.map_id_apply]

/-- (U1) The universal property of the cone against the décalage model of the undercategory:
morphisms `K ⟶ X_{c/}` correspond to morphisms `Δ[0] ⋆ K ⟶ X` sending the cone point to `c`.
Under this bijection `g ≫ X.underProj c = coneι K ≫ ĝ` (`coneι_comp_toCone`), and it is
natural in `K` (`toCone_naturality`). -/
@[simps]
def coneHomEquiv (K : SSet.{u}) (X : SSet.{u}) (c : X _⦋0⦌) :
    (K ⟶ (X.under c : SSet.{u})) ≃ {f : cone K ⟶ X // conePt K ≫ f = const c} where
  toFun g := ⟨toCone g, conePt_comp_toCone g⟩
  invFun f := fromCone f.1 f.2
  left_inv g := fromCone_toCone g
  right_inv f := Subtype.ext (toCone_fromCone f.1 f.2)

end UniversalProperty

/-! ### (C2) Subcomplexes of the cone -/

namespace ConeSimplex

variable {K : SSet.{u}}

lemma mapHom_injective {L : SSet.{u}} (f : K ⟶ L) [Mono f] {n : ℕ} :
    Function.Injective (mapHom f (n := n)) := by
  rintro ⟨j, k, hjk, y⟩ ⟨j', k', hjk', y'⟩ h
  simp only [mapHom, mk.injEq] at h
  obtain ⟨rfl, rfl, hy⟩ := h
  refine ext_of_j_eq rfl (heq_of_eq ?_)
  have hy := eq_of_heq hy
  cases k with
  | zero => rfl
  | succ k =>
    have hinj : Function.Injective (f.app (op ⦋k⦌)) :=
      (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance _)
    exact hinj hy

lemma ofSimplex_injective {n : ℕ} : Function.Injective (ofSimplex (K := K) (n := n)) := by
  intro y y' h
  exact eq_of_heq (ConeSimplex.mk.inj h).2.2

end ConeSimplex

instance coneMap_mono {K L : SSet.{u}} (f : K ⟶ L) [Mono f] : Mono (coneMap f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  exact ConeSimplex.mapHom_injective f

instance coneι_mono (K : SSet.{u}) : Mono (coneι K) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  exact ConeSimplex.ofSimplex_injective

namespace Subcomplex

variable {K : SSet.{u}}

/-- Membership in the augmented subcomplex `A⁺ ⊆ K⁺` (`A⁺ 0 = pt`). -/
def augMem (A : K.Subcomplex) : ∀ {k : ℕ}, K.aug k → Prop
  | 0, _ => True
  | k + 1, y => y ∈ A.obj (op ⦋k⦌)

lemma augMem_augMap (A : K.Subcomplex) {a b : ℕ} (ρ : Fin a →o Fin b) {y : K.aug b}
    (hy : A.augMem y) : A.augMem (K.augMap ρ y) := by
  cases a with
  | zero => trivial
  | succ a =>
    cases b with
    | zero => exact (ρ 0).elim0
    | succ b => exact A.map _ hy

lemma augMem_sup (A B : K.Subcomplex) {k : ℕ} (y : K.aug k) :
    (A ⊔ B).augMem y ↔ A.augMem y ∨ B.augMem y := by
  cases k with
  | zero => simp [augMem]
  | succ k => exact Iff.rfl

lemma augMem_inf (A B : K.Subcomplex) {k : ℕ} (y : K.aug k) :
    (A ⊓ B).augMem y ↔ A.augMem y ∧ B.augMem y := by
  cases k with
  | zero => simp [augMem]
  | succ k => exact Iff.rfl

lemma augMem_top {k : ℕ} (y : K.aug k) : (⊤ : K.Subcomplex).augMem y := by
  cases k with
  | zero => trivial
  | succ k => exact Set.mem_univ _

lemma augMem_mono {A B : K.Subcomplex} (h : A ≤ B) {k : ℕ} {y : K.aug k} (hy : A.augMem y) :
    B.augMem y := by
  cases k with
  | zero => trivial
  | succ k => exact h _ hy

/-- (C2) `Δ[0] ⋆ A` as a subcomplex of `Δ[0] ⋆ K`: the simplices whose residual simplex lies
in `A`. -/
def cone (A : K.Subcomplex) : (SSet.cone K).Subcomplex where
  obj _ := {x | A.augMem x.y}
  map _ _ hx := A.augMem_augMap _ hx

lemma mem_cone_iff (A : K.Subcomplex) {n : SimplexCategoryᵒᵖ} (x : (SSet.cone K).obj n) :
    x ∈ (cone A).obj n ↔ A.augMem x.y := Iff.rfl

lemma cone_sup (A B : K.Subcomplex) : cone (A ⊔ B) = cone A ⊔ cone B :=
  le_antisymm (fun _ _ hx ↦ (augMem_sup A B _).1 hx) (fun _ _ hx ↦ (augMem_sup A B _).2 hx)

lemma cone_inf (A B : K.Subcomplex) : cone (A ⊓ B) = cone A ⊓ cone B :=
  le_antisymm (fun _ _ hx ↦ (augMem_inf A B _).1 hx) (fun _ _ hx ↦ (augMem_inf A B _).2 hx)

lemma cone_top : cone (⊤ : K.Subcomplex) = ⊤ :=
  le_antisymm le_top (fun _ _ _ ↦ augMem_top _)

lemma cone_mono {A B : K.Subcomplex} (h : A ≤ B) : cone A ≤ cone B :=
  fun _ _ hx ↦ augMem_mono h hx

lemma pt_mem_cone (A : K.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    ConeSimplex.pt K n.unop.len ∈ (cone A).obj n := trivial

lemma ofSimplex_mem_cone_iff (A : K.Subcomplex) {n : ℕ} (y : K _⦋n⦌) :
    ConeSimplex.ofSimplex y ∈ (cone A).obj (op ⦋n⦌) ↔ y ∈ A.obj (op ⦋n⦌) := Iff.rfl

/-- The lift of `y ∈ A⁺` to `(A : SSet)⁺`. -/
def augLift (A : K.Subcomplex) : ∀ {k : ℕ} (y : K.aug k), A.augMem y → (A : SSet.{u}).aug k
  | 0, _, _ => PUnit.unit
  | _ + 1, y, hy => ⟨y, hy⟩

lemma augHom_ι_augLift (A : K.Subcomplex) {k : ℕ} (y : K.aug k) (hy : A.augMem y) :
    augHom A.ι (A.augLift y hy) = y := by
  cases k <;> rfl

lemma augMem_augHom_ι (A : K.Subcomplex) {k : ℕ} (y : (A : SSet.{u}).aug k) :
    A.augMem (augHom A.ι y) := by
  cases k with
  | zero => trivial
  | succ k => exact y.2

lemma augLift_augHom_ι (A : K.Subcomplex) {k : ℕ} (y : (A : SSet.{u}).aug k) :
    A.augLift (augHom A.ι y) (augMem_augHom_ι A y) = y := by
  cases k <;> rfl

lemma augLift_augMap (A : K.Subcomplex) {a b : ℕ} (ρ : Fin a →o Fin b) (y : K.aug b)
    (hy : A.augMem y) :
    A.augLift (K.augMap ρ y) (A.augMem_augMap ρ hy) = (A : SSet.{u}).augMap ρ (A.augLift y hy) := by
  cases a with
  | zero => rfl
  | succ a =>
    cases b with
    | zero => exact (ρ 0).elim0
    | succ b => rfl

lemma range_coneMap_ι (A : K.Subcomplex) : range (coneMap A.ι) = cone A := by
  refine le_antisymm ?_ ?_
  · rintro n _ ⟨x, rfl⟩
    exact augMem_augHom_ι A x.y
  · intro n x hx
    exact ⟨⟨x.j, x.k, x.hjk, A.augLift x.y hx⟩,
      ConeSimplex.ext_of_j_eq rfl (heq_of_eq (augHom_ι_augLift A x.y hx))⟩

/-- The identification `Δ[0] ⋆ A ⟶ Subcomplex.cone A` (an isomorphism, inverse `coneLift`). -/
def coneToSub (A : K.Subcomplex) : SSet.cone (A : SSet.{u}) ⟶ (cone A : SSet.{u}) :=
  Subcomplex.lift (coneMap A.ι) (by rw [range_coneMap_ι])

lemma coneToSub_ι (A : K.Subcomplex) : coneToSub A ≫ (cone A).ι = coneMap A.ι := rfl

/-- The identification `Subcomplex.cone A ⟶ Δ[0] ⋆ A` (an isomorphism, inverse `coneToSub`). -/
@[simps!]
def coneLift (A : K.Subcomplex) : (cone A : SSet.{u}) ⟶ SSet.cone (A : SSet.{u}) where
  app _ := ↾fun x ↦ ⟨x.1.j, x.1.k, x.1.hjk, A.augLift x.1.y x.2⟩
  naturality _ _ α := ConcreteCategory.hom_ext _ _ fun x ↦ by
    refine ConeSimplex.ext_of_j_eq ?_ ?_
    · rfl
    · exact heq_of_eq (augLift_augMap A _ _ _)

lemma coneLift_coneMap_ι (A : K.Subcomplex) : coneLift A ≫ coneMap A.ι = (cone A).ι :=
  NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun x ↦ by
    refine ConeSimplex.ext_of_j_eq ?_ ?_
    · rfl
    · exact heq_of_eq (augHom_ι_augLift A _ _))

lemma coneToSub_coneLift (A : K.Subcomplex) : coneToSub A ≫ coneLift A = 𝟙 _ :=
  NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun x ↦ by
    refine ConeSimplex.ext_of_j_eq ?_ ?_
    · rfl
    · exact heq_of_eq (augLift_augHom_ι A _))

lemma coneLift_coneToSub (A : K.Subcomplex) : coneLift A ≫ coneToSub A = 𝟙 _ := by
  rw [← cancel_mono (cone A).ι, Category.assoc, coneToSub_ι, coneLift_coneMap_ι,
    Category.id_comp]

/-- The simplices of `Δ[0] ⋆ K` in the base `∅ ⋆ K`: those with `j = 0`. -/
lemma mem_range_coneι_iff {n : SimplexCategoryᵒᵖ} (x : (SSet.cone K).obj n) :
    x ∈ (range (coneι K)).obj n ↔ x.j = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    obtain ⟨j, k, hjk, y⟩ := x
    dsimp only at hx
    subst hx
    obtain rfl : k = n.unop.len + 1 := by omega
    exact ⟨y, rfl⟩

lemma pt_not_mem_range_coneι (n : SimplexCategoryᵒᵖ) :
    ConeSimplex.pt K n.unop.len ∉ (range (coneι K)).obj n :=
  fun h ↦ Nat.succ_ne_zero _ ((mem_range_coneι_iff _).1 h)

end Subcomplex

/-! ### (U2) [Lur09, Lemma 2.1.2.3] and the left fibration `X_{c/} ⟶ X` -/

/-- The statement of [Lur09, Lemma 2.1.2.3] (if `B₀ ↪ B` is left anodyne then
`(Δ[0] ⋆ B₀) ∪ (∅ ⋆ B) ↪ Δ[0] ⋆ B` is inner anodyne), taken as a hypothesis below; it is
proved as `SSet.innerAnodyneConeOfLeftAnodyne` in `Join/ConeLifting.lean` and
re-exported as `SSet.HTT.innerAnodyne_cone_of_leftAnodyne`. -/
def InnerAnodyneConeOfLeftAnodyne : Prop :=
  ∀ {B : SSet.{u}} (B₀ : B.Subcomplex), leftAnodyneExtensions B₀.ι →
    innerAnodyneExtensions (Subcomplex.cone B₀ ⊔ Subcomplex.range (coneι B)).ι

open Limits in
/-- The lifting problem of [Lur09, 2.1.2.2] for a single left horn, solved from the statement
of [Lur09, 2.1.2.3], taken as the hypothesis `H`, and the universal property `coneHomEquiv`.

This is the case `B = Δ[0]` of `hasLiftingProperty_relUnderProj` (`Join/ConeLifting.lean`),
where `relUnderProj p c` is `C.underProj c` up to isomorphism. It is proved separately because
`Cone.lean` comes first. -/
lemma hasLiftingProperty_horn_ι_underProj (H : InnerAnodyneConeOfLeftAnodyne.{u})
    (C : SSet.{u}) [Quasicategory C] (c : C _⦋0⦌)
    {n : ℕ} (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty Λ[n + 1, i].ι (C.underProj c) := by
  constructor
  intro a b sq
  -- the map `(Δ[0] ⋆ Λ[n + 1, i]) ∪ (∅ ⋆ Δ[n + 1]) ⟶ C` glued from `toCone a` and `b`
  have bsq : Subcomplex.BicartSq
      (Subcomplex.cone Λ[n + 1, i] ⊓ Subcomplex.range (coneι Δ[n + 1]))
      (Subcomplex.cone Λ[n + 1, i]) (Subcomplex.range (coneι Δ[n + 1]))
      (Subcomplex.cone Λ[n + 1, i] ⊔ Subcomplex.range (coneι Δ[n + 1])) := ⟨rfl, rfl⟩
  have hφ₂ : Subcomplex.toRange (coneι Δ[n + 1]) ≫
      (inv (Subcomplex.toRange (coneι Δ[n + 1])) ≫ b) = b := by
    simp only [IsIso.hom_inv_id_assoc]
  have w : Subcomplex.homOfLE bsq.le₁₂ ≫ (Subcomplex.coneLift Λ[n + 1, i] ≫ toCone a) =
      Subcomplex.homOfLE bsq.le₁₃ ≫ (inv (Subcomplex.toRange (coneι Δ[n + 1])) ≫ b) := by
    refine NatTrans.ext (funext fun m ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
    obtain ⟨x, hx₁, y, rfl⟩ := x
    have h₂ := ConcreteCategory.congr_hom (NatTrans.congr_app hφ₂ m) y
    change (inv (Subcomplex.toRange (coneι Δ[n + 1])) ≫ b).app m ⟨(coneι _).app m y, y, rfl⟩ =
      b.app m y at h₂
    change toConeFun a (ConeSimplex.ofSimplex ⟨y, hx₁⟩) =
      (inv (Subcomplex.toRange (coneι Δ[n + 1])) ≫ b).app m ⟨(coneι _).app m y, y, rfl⟩
    rw [h₂]
    have h₁ := ConcreteCategory.congr_hom (NatTrans.congr_app (coneι_comp_toCone a) m) ⟨y, hx₁⟩
    change toConeFun a (ConeSimplex.ofSimplex ⟨y, hx₁⟩) =
      (C.underProj c).app m (a.app m ⟨y, hx₁⟩) at h₁
    rw [h₁]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app sq.w m) ⟨y, hx₁⟩
  have hφ₁ := bsq.isPushout.inl_desc _ _ w
  have hφ₂' := bsq.isPushout.inr_desc _ _ w
  -- the extension to `Δ[0] ⋆ Δ[n + 1]`
  have hU := H Λ[n + 1, i] (leftAnodyneExtensions.horn_ι hi)
  have hlift : HasLiftingProperty
      (Subcomplex.cone Λ[n + 1, i] ⊔ Subcomplex.range (coneι Δ[n + 1])).ι (terminal.from C) :=
    hU _ (mem_innerFibrations _)
  have sq' : CommSq (bsq.isPushout.desc _ _ w)
      (Subcomplex.cone Λ[n + 1, i] ⊔ Subcomplex.range (coneι Δ[n + 1])).ι
      (terminal.from C) (terminal.from _) := ⟨terminalIsTerminal.hom_ext _ _⟩
  have hℓ := sq'.fac_left
  have hℓpt : conePt _ ≫ sq'.lift = const c := by
    refine NatTrans.ext (funext fun m ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_)
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hℓ m)
      ⟨ConeSimplex.pt _ m.unop.len, Or.inl (Subcomplex.pt_mem_cone Λ[n + 1, i] m)⟩
    change sq'.lift.app m (ConeSimplex.pt _ m.unop.len) = (bsq.isPushout.desc _ _ w).app m ⟨_, _⟩
      at h
    have h' := ConcreteCategory.congr_hom (NatTrans.congr_app hφ₁ m)
      ⟨ConeSimplex.pt _ m.unop.len, Subcomplex.pt_mem_cone Λ[n + 1, i] m⟩
    change (bsq.isPushout.desc _ _ w).app m ⟨_, _⟩ = toConeFun a (ConeSimplex.pt _ m.unop.len) at h'
    change sq'.lift.app m (ConeSimplex.pt _ m.unop.len) = (const c : Δ[0] ⟶ C).app m t
    rw [h, h']
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (conePt_comp_toCone a) m) t
  refine ⟨⟨⟨fromCone sq'.lift hℓpt, ?_, ?_⟩⟩⟩
  · -- `Λ[n + 1, i].ι ≫ lift = a`
    apply (coneHomEquiv _ C c).injective
    refine Subtype.ext ?_
    change toCone (Λ[n + 1, i].ι ≫ fromCone sq'.lift hℓpt) = toCone a
    rw [toCone_naturality, toCone_fromCone]
    calc coneMap Λ[n + 1, i].ι ≫ sq'.lift
        = Subcomplex.coneToSub Λ[n + 1, i] ≫ (Subcomplex.cone Λ[n + 1, i]).ι ≫ sq'.lift := by
          rw [← Category.assoc, Subcomplex.coneToSub_ι]
      _ = Subcomplex.coneToSub Λ[n + 1, i] ≫ Subcomplex.homOfLE bsq.le₂₄ ≫
            (Subcomplex.cone Λ[n + 1, i] ⊔ Subcomplex.range (coneι Δ[n + 1])).ι ≫ sq'.lift := rfl
      _ = Subcomplex.coneToSub Λ[n + 1, i] ≫ (Subcomplex.coneLift Λ[n + 1, i] ≫ toCone a) := by
          rw [hℓ, hφ₁]
      _ = toCone a := by
          rw [← Category.assoc, Subcomplex.coneToSub_coneLift, Category.id_comp]
  · -- `lift ≫ underProj c = b`
    rw [← coneι_comp_toCone, toCone_fromCone]
    calc coneι Δ[n + 1] ≫ sq'.lift
        = Subcomplex.toRange (coneι Δ[n + 1]) ≫ (Subcomplex.range (coneι Δ[n + 1])).ι ≫
            sq'.lift := rfl
      _ = Subcomplex.toRange (coneι Δ[n + 1]) ≫ Subcomplex.homOfLE bsq.le₃₄ ≫
            (Subcomplex.cone Λ[n + 1, i] ⊔ Subcomplex.range (coneι Δ[n + 1])).ι ≫ sq'.lift := rfl
      _ = Subcomplex.toRange (coneι Δ[n + 1]) ≫
            (inv (Subcomplex.toRange (coneι Δ[n + 1])) ≫ b) := by
          rw [hℓ, hφ₂']
      _ = b := hφ₂

/-- [Lur09, Proposition 2.1.2.2], derived from the statement of [Lur09, 2.1.2.3] (the
hypothesis `H`) and the universal property `coneHomEquiv`: for an ∞-category `C` and an object
`c`, the projection `C_{c/} ⟶ C` is a left fibration. The hypothesis is discharged by
`SSet.innerAnodyneConeOfLeftAnodyne` (`Join/ConeLifting.lean`); the unconditional
statement is `SSet.HTT.leftFibration_underProj` (`Cofinal/HTT.lean`). -/
theorem leftFibration_underProj_of_innerAnodyne_cone (H : InnerAnodyneConeOfLeftAnodyne.{u})
    (C : SSet.{u}) [Quasicategory C] (c : C _⦋0⦌) : LeftFibration (C.underProj c) := by
  constructor
  rintro _ _ _ ⟨i, hi⟩
  exact hasLiftingProperty_horn_ι_underProj H C c i hi

/-! ### Naturality of the universal property in `X` -/

/-- The décalage of a morphism. -/
@[simps]
def decMap {X Y : SSet.{u}} (F : X ⟶ Y) : X.dec ⟶ Y.dec where
  app n := F.app (op ⦋n.unop.len + 1⦌)
  naturality _ _ _ := F.naturality _

lemma decVertex_decMap {X Y : SSet.{u}} (F : X ⟶ Y) {n : SimplexCategoryᵒᵖ} (x : X.dec.obj n) :
    Y.decVertex ((decMap F).app n x) = F.app _ (X.decVertex x) :=
  (NatTrans.naturality_apply F _ x).symm

/-- The morphism `X_{c/} ⟶ Y_{F c/}` induced by `F : X ⟶ Y`. -/
@[simps!]
def underMap {X Y : SSet.{u}} (F : X ⟶ Y) (c : X _⦋0⦌) :
    (X.under c : SSet.{u}) ⟶ (Y.under (F.app _ c) : SSet.{u}) where
  app n := ↾fun x ↦ ⟨(decMap F).app n x.1, by
    change Y.decVertex _ = _
    rw [decVertex_decMap, x.2]⟩
  naturality _ _ α := ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext
    (NatTrans.naturality_apply F _ x.1)

lemma underMap_underProj {X Y : SSet.{u}} (F : X ⟶ Y) (c : X _⦋0⦌) :
    underMap F c ≫ Y.underProj (F.app _ c) = X.underProj c ≫ F :=
  NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun x ↦ by
    change Y.map (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op (F.app _ x.1) =
      F.app n (X.map (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op x.1)
    exact (NatTrans.naturality_apply F _ x.1).symm)

lemma decAug_comp_underMap {K X Y : SSet.{u}} {c : X _⦋0⦌} (g : K ⟶ (X.under c : SSet.{u}))
    (F : X ⟶ Y) {k : ℕ} (y : K.aug k) :
    decAug (g ≫ underMap F c) y = F.app _ (decAug g y) := by
  cases k <;> rfl

/-- Naturality of `toCone` in `X`. -/
lemma toCone_naturality_right {K X Y : SSet.{u}} {c : X _⦋0⦌} (g : K ⟶ (X.under c : SSet.{u}))
    (F : X ⟶ Y) : toCone (g ≫ underMap F c) = toCone g ≫ F := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  change Y.map _ (decAug (g ≫ underMap F c) x.y) = F.app n (X.map _ (decAug g x.y))
  rw [decAug_comp_underMap, NatTrans.naturality_apply]

/-! ### (C1) `Δ[0] ⋆ Δ[m] ≅ Δ[m + 1]` -/

namespace stdSimplex

/-- The vertex `0` of `Δ[m + 1]`. -/
abbrev vertex₀ (m : ℕ) : Δ[m + 1] _⦋0⦌ := obj₀Equiv.symm 0

/-- The augmented version of `Δ[0] ⋆ (−)` on `Δ[m]⁺ k`: a monotone map
`Fin (k + 1) →o Fin (m + 2)`. -/
def coneAug (m : ℕ) : ∀ {k : ℕ}, Δ[m].aug k → (Fin (k + 1) →o Fin (m + 2))
  | 0, _ => OrderHom.const _ 0
  | _ + 1, y => SimplexCategory.coneShiftFun (asOrderHom y)

lemma coneAug_eq_zero_iff (m : ℕ) {k : ℕ} (y : Δ[m].aug k) (t : Fin (k + 1)) :
    coneAug m y t = 0 ↔ t = 0 := by
  cases k with
  | zero => exact ⟨fun _ ↦ Subsingleton.elim (α := Fin 1) _ _, fun _ ↦ rfl⟩
  | succ k =>
    change SimplexCategory.coneShiftFun (asOrderHom y) t = 0 ↔ t = 0
    induction t using Fin.cases with
    | zero => simp
    | succ s => simp [Fin.succ_ne_zero]

lemma coneAug_augHom_map (m m' : ℕ) (f : ⦋m⦌ ⟶ ⦋m'⦌) {k : ℕ} (y : Δ[m].aug k) :
    coneAug m' (augHom (stdSimplex.map f) y) =
      (SimplexCategory.coneShiftHom f).toOrderHom.comp (coneAug m y) := by
  cases k with
  | zero =>
    refine OrderHom.ext _ _ (funext fun t ↦ ?_)
    change (0 : Fin (m' + 2)) = SimplexCategory.coneShiftFun f.toOrderHom 0
    rfl
  | succ k =>
    change SimplexCategory.coneShiftFun (f.toOrderHom.comp (asOrderHom y)) = _
    rw [SimplexCategory.coneShiftFun_comp]
    rfl

/-- `Δ[m] ⟶ Δ[m + 1]_{0/}`, `y ↦ 0 ⋆ y`. -/
@[simps!]
def toUnderVertex₀ (m : ℕ) : Δ[m] ⟶ (Δ[m + 1].under (vertex₀ m) : SSet.{u}) where
  app n := ↾fun y ↦ ⟨objMk (SimplexCategory.coneShiftFun (asOrderHom y)), by
    change Δ[m + 1].map _ (objMk _) = _
    exact stdSimplex.ext _ _ fun i ↦ rfl⟩
  naturality n n' α := ConcreteCategory.hom_ext _ _ fun y ↦ Subtype.ext (by
    change objMk (n := ⦋m + 1⦌) (m := op ⦋n'.unop.len + 1⦌)
        (SimplexCategory.coneShiftFun ((asOrderHom y).comp α.unop.toOrderHom)) =
      Δ[m + 1].map (SimplexCategory.coneShiftHom α.unop).op
        (objMk (n := ⦋m + 1⦌) (m := op ⦋n.unop.len + 1⦌)
          (SimplexCategory.coneShiftFun (asOrderHom y)))
    exact stdSimplex.ext _ _ fun i ↦ by
      induction i using Fin.cases <;> rfl)

lemma decAug_toUnderVertex₀ (m : ℕ) {k : ℕ} (y : Δ[m].aug k) :
    decAug (toUnderVertex₀ m) y = objMk (coneAug m y) := by
  cases k <;> rfl

/-- The identity simplex of `Δ[m]`. -/
abbrev idSimplex (m : ℕ) : Δ[m] _⦋m⦌ := objEquiv.symm (𝟙 _)

lemma toConeFun_toUnderVertex₀ (m : ℕ) {n : ℕ} (x : Δ[m].ConeSimplex n) :
    toConeFun (toUnderVertex₀ m) x = objMk ((coneAug m x.y).comp (collapse x.j x.k x.hjk)) := by
  change Δ[m + 1].map _ (decAug (toUnderVertex₀ m) x.y) = _
  rw [decAug_toUnderVertex₀]
  rfl

/-- The key computation for (C1): `(0 ⋆ id) ⋅ (coneAug y ∘ collapse) = x`. -/
lemma cons_idSimplex_map (m : ℕ) {n : ℕ} (x : Δ[m].ConeSimplex n) :
    (ConeSimplex.cons (idSimplex m)).map ((coneAug m x.y).comp (collapse x.j x.k x.hjk)) = x := by
  have hc : cut ((coneAug m x.y).comp (collapse x.j x.k x.hjk)) 1 = x.j :=
    Nat.eq_of_forall_fin_lt_iff (cut_le _ _) (by have := x.hjk; omega) fun i ↦ by
      rw [lt_cut_iff, Nat.lt_one_iff]
      change ((coneAug m x.y) (collapse x.j x.k x.hjk i) : ℕ) = 0 ↔ _
      have h1 := coneAug_eq_zero_iff m x.y (collapse x.j x.k x.hjk i)
      rw [Fin.ext_iff, Fin.ext_iff, collapse_apply_val] at h1
      simp only [Fin.val_zero] at h1
      rw [h1]
      omega
  obtain ⟨j, k, hjk, y⟩ := x
  dsimp only at hc ⊢
  refine ConeSimplex.ext_of_j_eq hc ?_
  cases k with
  | zero =>
    refine HEq.trans (augMap_congr Δ[m] (a' := 0) (by omega)
      (residual _ 1 (m + 1) (by omega)) (emptyOrderHom (m + 1))
      (fun i ↦ absurd i.isLt (by omega)) _) ?_
    exact heq_of_eq rfl
  | succ k =>
    refine HEq.trans (augMap_congr Δ[m] (a' := k + 1) (by omega)
      (residual _ 1 (m + 1) (by omega)) (asOrderHom y) (fun i ↦ ?_) _) ?_
    · rw [residual_apply_val]
      have hi : (i : ℕ) < k + 1 := by
        have := i.isLt; change (i : ℕ) < n + 1 - cut _ 1 at this; omega
      change (SimplexCategory.coneShiftFun (asOrderHom y) (collapse j (k + 1) hjk
        ⟨i + cut _ 1, _⟩) : ℕ) - 1 = _
      have h2 : collapse j (k + 1) hjk ⟨i + cut ((coneAug m y).comp (collapse j (k + 1) hjk)) 1,
          by have := i.isLt; omega⟩ = (⟨i, hi⟩ : Fin (k + 1)).succ :=
        Fin.ext (by rw [collapse_apply_val]; simp; omega)
      rw [h2, SimplexCategory.coneShiftFun_succ]
      simp only [Fin.val_succ, Nat.add_sub_cancel]
      rfl
    · exact heq_of_eq (stdSimplex.ext _ _ fun i ↦ rfl)

/-- (C1) `Δ[0] ⋆ Δ[m] ≅ Δ[m + 1]`. The forward map is `toCone (toUnderVertex₀ m)`, so that
`conePt_comp_toCone` and `coneι_comp_toCone` describe the cone point and the base. -/
@[simps]
def coneIso (m : ℕ) : cone (Δ[m] : SSet.{u}) ≅ Δ[m + 1] where
  hom := toCone (toUnderVertex₀ m)
  inv := yonedaEquiv.symm (ConeSimplex.cons (idSimplex.{u} m))
  hom_inv_id := by
    refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
    change (cone Δ[m]).map (objEquiv (toConeFun (toUnderVertex₀ m) x)).op
      (ConeSimplex.cons (idSimplex m)) = x
    exact (congrArg (fun z : (Δ[m + 1] : SSet.{u}) _⦋n.unop.len⦌ ↦
      (cone (Δ[m] : SSet.{u})).map (objEquiv z).op
      (ConeSimplex.cons (idSimplex.{u} m) : (cone (Δ[m] : SSet.{u})).obj (op ⦋m + 1⦌)))
      (toConeFun_toUnderVertex₀ m x)).trans (cons_idSimplex_map m x)
  inv_hom_id := by
    apply yonedaEquiv.injective
    have h := (yonedaEquiv (X := cone (Δ[m] : SSet.{u})) (n := ⦋m + 1⦌)).apply_symm_apply
      (ConeSimplex.cons (idSimplex.{u} m))
    refine (congrArg (fun z ↦ (toCone (toUnderVertex₀ m)).app (op ⦋m + 1⦌) z) h).trans ?_
    change objMk (n := ⦋m + 1⦌) (m := op ⦋m + 1⦌)
      ((coneAug m (ConeSimplex.cons (idSimplex.{u} m)).y).comp
        (collapse 1 (m + 1) (by change 1 + (m + 1) = m + 1 + 1; omega))) =
      yonedaEquiv (𝟙 _)
    refine stdSimplex.ext _ _ fun i ↦ ?_
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl

lemma coneIso_hom_conePt (m : ℕ) : conePt Δ[m] ≫ (coneIso m).hom = SSet.const (vertex₀ m) :=
  conePt_comp_toCone _

lemma coneIso_hom_coneι (m : ℕ) :
    coneι Δ[m] ≫ (coneIso m).hom = stdSimplex.map (SimplexCategory.δ 0) := by
  rw [coneIso_hom, coneι_comp_toCone]
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun y ↦ ?_)
  exact stdSimplex.ext _ _ fun i ↦ rfl

/-- (C1), compatibility with `coneShiftHom`. -/
lemma coneMap_map_coneIso_hom {m m' : ℕ} (f : ⦋m⦌ ⟶ ⦋m'⦌) :
    coneMap (stdSimplex.map f) ≫ (coneIso m').hom =
      (coneIso m).hom ≫ stdSimplex.map (SimplexCategory.coneShiftHom f) := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  obtain ⟨j, k, hjk, y⟩ := x
  change toConeFun (toUnderVertex₀ m') ⟨j, k, hjk, augHom (stdSimplex.map f) y⟩ =
    (stdSimplex.map (SimplexCategory.coneShiftHom f)).app n
      (toConeFun (toUnderVertex₀ m) ⟨j, k, hjk, y⟩)
  rw [toConeFun_toUnderVertex₀, toConeFun_toUnderVertex₀]
  change objMk (n := ⦋m' + 1⦌) (m := n)
    ((coneAug m' (augHom (stdSimplex.map f) y)).comp (collapse j k hjk)) = _
  rw [coneAug_augHom_map]
  rfl

end stdSimplex

/-! ### (C4) The horn case of (U2) -/

open stdSimplex in
/-- Under `stdSimplex.coneIso (n + 1) : Δ[0] ⋆ Δ[n + 1] ≅ Δ[n + 2]`, which carries the cone
point to the vertex `0` and `coneι` to `δ 0`, the subcomplex
`(Δ[0] ⋆ Λ[n + 1, i]) ∪ (∅ ⋆ Δ[n + 1])` of `Δ[0] ⋆ Δ[n + 1]` is the preimage of the horn
`Λ[n + 2, i.succ]`. -/
lemma cone_horn_sup_range_coneι {n : ℕ} (i : Fin (n + 2)) :
    Subcomplex.cone Λ[n + 1, i] ⊔ Subcomplex.range (coneι Δ[n + 1]) =
      Λ[n + 2, i.succ].preimage (stdSimplex.coneIso.{u} (n + 1)).hom := by
  ext m x
  obtain ⟨⟨p⟩⟩ := m
  rw [Subcomplex.preimage_obj, Set.mem_preimage,
    show (ConcreteCategory.hom ((coneIso.{u} (n + 1)).hom.app (op ⦋p⦌))) x
        = objMk ((coneAug (n + 1) x.y).comp (collapse x.j x.k x.hjk)) from
      toConeFun_toUnderVertex₀ _ _,
    mem_horn_iff_notMem_range, Subfunctor.max_obj, Set.mem_union,
    Subcomplex.mem_cone_iff, Subcomplex.mem_range_coneι_iff]
  obtain ⟨j, k, hjk, y⟩ := x
  dsimp only at hjk ⊢
  rw [show Set.range
      ⇑(objMk ((coneAug (n + 1) y).comp (collapse j k hjk)) : Δ[n + 2] _⦋p⦌) =
      Set.range (fun t ↦ coneAug (n + 1) y (collapse j k hjk t)) from rfl]
  cases k with
  | zero =>
    obtain ⟨v, hv⟩ := exists_ne i
    refine iff_of_true (Or.inl trivial) ⟨v.succ, fun h ↦ hv (Fin.succ_inj.1 h), ?_⟩
    rintro ⟨t, ht⟩
    exact Fin.succ_ne_zero v ht.symm
  | succ k' =>
    have hzero : coneAug (n + 1) y 0 = 0 := (coneAug_eq_zero_iff _ y 0).2 rfl
    have hsucc : ∀ t : Fin (k' + 1), coneAug (n + 1) y t.succ = (asOrderHom y t).succ :=
      fun _ ↦ rfl
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · refine iff_of_true (Or.inr rfl) ⟨0, (Fin.succ_ne_zero i).symm, ?_⟩
      rintro ⟨t, ht⟩
      have h : collapse 0 (k' + 1) hjk t ≠ 0 := by
        rw [Ne, Fin.ext_iff, collapse_apply_val]
        simp
      exact h ((coneAug_eq_zero_iff _ y _).1 ht)
    · rw [or_iff_left (show j ≠ 0 by omega)]
      refine Iff.trans (mem_horn_iff_notMem_range (n := n + 1) (d := k') y i) ?_
      constructor
      · rintro ⟨v, hv, hvr⟩
        refine ⟨v.succ, fun h ↦ hv (Fin.succ_inj.1 h), ?_⟩
        rintro ⟨t, ht⟩
        dsimp only at ht
        rcases Fin.eq_zero_or_eq_succ (collapse j (k' + 1) hjk t) with h | ⟨s, h⟩
        · rw [h, hzero] at ht
          exact Fin.succ_ne_zero v ht.symm
        · rw [h, hsucc] at ht
          exact hvr ⟨s, Fin.succ_inj.1 ht⟩
      · rintro ⟨w, hw, hwr⟩
        have h0 : w ≠ 0 := by
          rintro rfl
          refine hwr ⟨0, ?_⟩
          have h : collapse j (k' + 1) hjk 0 = 0 := by
            rw [Fin.ext_iff, collapse_apply_val]
            simp
            omega
          dsimp only
          rw [h, hzero]
        obtain ⟨v, rfl⟩ := Fin.eq_succ_of_ne_zero h0
        refine ⟨v, fun h ↦ hw (by rw [h]), ?_⟩
        rintro ⟨t, ht⟩
        have htlt : (t : ℕ) + j < p + 1 := by have := t.isLt; omega
        refine hwr ⟨⟨(t : ℕ) + j, htlt⟩, ?_⟩
        have hc : collapse j (k' + 1) hjk ⟨(t : ℕ) + j, htlt⟩ = t.succ := by
          rw [Fin.ext_iff, collapse_apply_val]
          simp only [Fin.val_succ]
          omega
        dsimp only
        rw [hc, hsucc]
        exact congrArg Fin.succ ht

/-- (U2) for a generating left horn inclusion: if `i < Fin.last (n + 1)` then
`(Δ[0] ⋆ Λ[n + 1, i]) ∪ (∅ ⋆ Δ[n + 1]) ↪ Δ[0] ⋆ Δ[n + 1]` is inner anodyne, being the inner
horn inclusion `Λ[n + 2, i.succ] ↪ Δ[n + 2]` transported along `stdSimplex.coneIso (n + 1)`
(the index `i.succ` is inner: `0 < i.succ` always, and `i.succ < Fin.last (n + 2)` exactly
because `i < Fin.last (n + 1)`). -/
lemma innerAnodyne_cone_horn {n : ℕ} (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    innerAnodyneExtensions
      (Subcomplex.cone Λ[n + 1, i] ⊔ Subcomplex.range (coneι Δ[n + 1])).ι := by
  rw [cone_horn_sup_range_coneι i]
  refine (innerAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (Subcomplex.preimageIso Λ[n + 2, i.succ] (stdSimplex.coneIso (n + 1)))
      (stdSimplex.coneIso (n + 1)) rfl)).2 (innerAnodyneExtensions.horn_ι (Fin.succ_pos i) ?_)
  rw [Fin.lt_def] at hi ⊢
  simp only [Fin.val_succ, Fin.val_last] at hi ⊢
  omega

/-! ### (C3) `Δ[0] ⋆ nerve V ≅ nerve (WithBot V)` for a preorder `V` -/

namespace nerveCone

variable {V : Type u} [Preorder V]

/-- The vertices of a simplex of `(nerve V)⁺`. -/
def augObj : ∀ {k : ℕ}, (nerve V).aug k → Fin k → V
  | 0, _ => Fin.elim0
  | _ + 1, F => F.obj

lemma augObj_monotone {k : ℕ} (y : (nerve V).aug k) : Monotone (augObj y) := by
  cases k with
  | zero => exact fun i ↦ i.elim0
  | succ k => exact (y : Fin (k + 1) ⥤ V).monotone

lemma augObj_augMap {a b : ℕ} (ρ : Fin a →o Fin b) (y : (nerve V).aug b) (i : Fin a) :
    augObj ((nerve V).augMap ρ y) i = augObj y (ρ i) := by
  cases a with
  | zero => exact i.elim0
  | succ a =>
    cases b with
    | zero => exact (ρ 0).elim0
    | succ b => rfl

/-- The simplex of `(nerve V)⁺` with given vertices. -/
def augMk : ∀ {k : ℕ}, (Fin k →o V) → (nerve V).aug k
  | 0, _ => PUnit.unit
  | _ + 1, f => f.monotone.functor

lemma augObj_augMk {k : ℕ} (f : Fin k →o V) (i : Fin k) : augObj (augMk f) i = f i := by
  cases k with
  | zero => exact i.elim0
  | succ k => rfl

lemma augMk_augObj {k : ℕ} (y : (nerve V).aug k) :
    augMk ⟨augObj y, augObj_monotone y⟩ = y := by
  cases k with
  | zero => rfl
  | succ k => exact nerve.ext_of_isThin rfl

lemma augMk_congr {k k' : ℕ} (h : k = k') (f : Fin k →o V) (f' : Fin k' →o V)
    (hf : ∀ i, f i = f' (Fin.cast h i)) : HEq (augMk f) (augMk f') := by
  subst h
  have : f = f' := OrderHom.ext _ _ (funext hf)
  subst this
  rfl

/-- The vertices of the simplex of `nerve (WithBot V)` associated with a simplex of the cone:
`⊥` on the first `j` vertices, then the vertices of `y`. -/
def toFun {n : ℕ} (x : (nerve V).ConeSimplex n) (i : Fin (n + 1)) : WithBot V :=
  if h : (i : ℕ) < x.j then ⊥
  else ↑(augObj x.y ⟨i - x.j, by have := x.hjk; have := i.isLt; omega⟩)

lemma toFun_of_lt {n : ℕ} (x : (nerve V).ConeSimplex n) (i : Fin (n + 1)) (h : (i : ℕ) < x.j) :
    toFun x i = ⊥ := by simp only [toFun, h, ↓reduceDIte]

lemma toFun_of_le {n : ℕ} (x : (nerve V).ConeSimplex n) (i : Fin (n + 1)) (h : x.j ≤ i) :
    toFun x i = ↑(augObj x.y ⟨i - x.j, by have := x.hjk; have := i.isLt; omega⟩) :=
  by simp only [toFun, not_lt.2 h, ↓reduceDIte]

lemma toFun_eq_bot_iff {n : ℕ} (x : (nerve V).ConeSimplex n) (i : Fin (n + 1)) :
    toFun x i = ⊥ ↔ (i : ℕ) < x.j := by
  by_cases h : (i : ℕ) < x.j
  · simp [toFun_of_lt x i h, h]
  · simp [toFun_of_le x i (not_lt.1 h), h]

lemma toFun_monotone {n : ℕ} (x : (nerve V).ConeSimplex n) : Monotone (toFun x) := by
  intro i i' hii'
  have hii'' : (i : ℕ) ≤ i' := hii'
  by_cases h : (i' : ℕ) < x.j
  · rw [toFun_of_lt x i (by omega), toFun_of_lt x i' h]
  · by_cases h' : (i : ℕ) < x.j
    · rw [toFun_of_lt x i h']
      exact bot_le
    · rw [toFun_of_le x i (not_lt.1 h'), toFun_of_le x i' (not_lt.1 h)]
      exact WithBot.coe_le_coe.2 (augObj_monotone x.y (Fin.mk_le_mk.2 (by omega)))

/-- The simplex of `nerve (WithBot V)` associated with a simplex of `Δ[0] ⋆ nerve V`. -/
def homFun {n : ℕ} (x : (nerve V).ConeSimplex n) : (nerve (WithBot V)).obj (op ⦋n⦌) :=
  (toFun_monotone x).functor

lemma homFun_obj {n : ℕ} (x : (nerve V).ConeSimplex n) (i : Fin (n + 1)) :
    (homFun x).obj i = toFun x i := rfl

lemma homFun_map {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (x : (nerve V).ConeSimplex n) :
    homFun (x.map α) = (nerve (WithBot V)).map (SimplexCategory.mkHom α).op (homFun x) := by
  refine nerve.ext_of_isThin (funext fun i ↦ ?_)
  change toFun (x.map α) i = toFun x (α i)
  by_cases h : (i : ℕ) < cut α x.j
  · rw [toFun_of_lt _ i h, toFun_of_lt x (α i) ((lt_cut_iff α x.j i).1 h)]
  · have h' := (lt_cut_iff α x.j i).not.1 h
    have hi : (i : ℕ) < m + 1 := i.isLt
    rw [toFun_of_le _ i (not_lt.1 h), toFun_of_le x (α i) (not_lt.1 h')]
    refine congrArg (fun v : V ↦ (↑v : WithBot V))
      ((augObj_augMap (residual α x.j x.k x.hjk) x.y ⟨i - cut α x.j, by omega⟩).trans ?_)
    refine congrArg (augObj x.y) (Fin.ext ?_)
    rw [residual_apply_val]
    have h2 : (⟨(⟨i - cut α x.j, by omega⟩ : Fin (m + 1 - cut α x.j)) + cut α x.j,
        by omega⟩ : Fin (m + 1)) = i :=
      Fin.ext (show (i : ℕ) - cut α x.j + cut α x.j = i by omega)
    rw [h2]

open Classical in
/-- The number of vertices of a simplex of `nerve (WithBot V)` equal to `⊥`. -/
noncomputable def botCut {n : ℕ} (F : (nerve (WithBot V)).obj (op ⦋n⦌)) : ℕ :=
  (Finset.univ.filter fun i : Fin (n + 1) ↦ F.obj i = ⊥).card

open Classical in
lemma botCut_le {n : ℕ} (F : (nerve (WithBot V)).obj (op ⦋n⦌)) : botCut F ≤ n + 1 :=
  (Finset.card_filter_le _ _).trans (by simp)

open Classical in
lemma lt_botCut_iff {n : ℕ} (F : (nerve (WithBot V)).obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    (i : ℕ) < botCut F ↔ F.obj i = ⊥ := by
  have hmono : Monotone F.obj := (F : Fin (n + 1) ⥤ WithBot V).monotone
  constructor
  · intro h
    by_contra h'
    have hsub : (Finset.univ.filter fun l : Fin (n + 1) ↦ F.obj l = ⊥) ⊆ Finset.Iio i := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [Finset.mem_Iio]
      by_contra hli
      exact h' (WithBot.le_bot_iff.1 (hl ▸ hmono (not_lt.1 hli)))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    exact absurd h (not_lt.2 this)
  · intro h
    have hsub : Finset.Iic i ⊆ (Finset.univ.filter fun l : Fin (n + 1) ↦ F.obj l = ⊥) := by
      intro l hl
      simp only [Finset.mem_Iic] at hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact WithBot.le_bot_iff.1 (h ▸ hmono hl)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    exact this

/-- The vertices not equal to `⊥` of a simplex of `nerve (WithBot V)`, as a monotone map. -/
noncomputable def invFun {n : ℕ} (F : (nerve (WithBot V)).obj (op ⦋n⦌)) :
    Fin (n + 1 - botCut F) →o V where
  toFun i := (F.obj (⟨i + botCut F, by have := i.isLt; omega⟩ : Fin (n + 1))).unbot
    ((lt_botCut_iff F (⟨i + botCut F, by have := i.isLt; omega⟩ : Fin (n + 1))).not.1
      (by show ¬ ((i : ℕ) + botCut F < botCut F); omega))
  monotone' i i' h := by
    have hmono : Monotone F.obj := (F : Fin (n + 1) ⥤ WithBot V).monotone
    refine WithBot.coe_le_coe.1 ?_
    rw [WithBot.coe_unbot, WithBot.coe_unbot]
    exact hmono (Fin.mk_le_mk.2 (by have := Fin.mk_le_mk.1 h; omega))

lemma coe_invFun {n : ℕ} (F : (nerve (WithBot V)).obj (op ⦋n⦌)) (i : Fin (n + 1 - botCut F)) :
    (invFun F i : WithBot V) = F.obj (⟨i + botCut F, by have := i.isLt; omega⟩ : Fin (n + 1)) :=
  WithBot.coe_unbot _ _

/-- The simplex of `Δ[0] ⋆ nerve V` associated with a simplex of `nerve (WithBot V)`. -/
noncomputable def invSimplex {n : ℕ} (F : (nerve (WithBot V)).obj (op ⦋n⦌)) :
    (nerve V).ConeSimplex n :=
  ⟨botCut F, n + 1 - botCut F, by have := botCut_le F; omega, augMk (invFun F)⟩

lemma invSimplex_homFun {n : ℕ} (x : (nerve V).ConeSimplex n) : invSimplex (homFun x) = x := by
  have hc : botCut (homFun x) = x.j :=
    Nat.eq_of_forall_fin_lt_iff (botCut_le _) (by have := x.hjk; omega) fun i ↦ by
      rw [lt_botCut_iff, homFun_obj, toFun_eq_bot_iff]
  refine ConeSimplex.ext_of_j_eq hc ?_
  refine HEq.trans (augMk_congr (k' := x.k) (by have := x.hjk; omega) (invFun (homFun x))
    ⟨augObj x.y, augObj_monotone x.y⟩ (fun i ↦ ?_)) (heq_of_eq (augMk_augObj x.y))
  refine WithBot.coe_injective ?_
  rw [coe_invFun, homFun_obj, toFun_of_le x _ (by dsimp only; omega)]
  exact congrArg (fun t : Fin x.k ↦ (↑(augObj x.y t) : WithBot V)) (Fin.ext (by simp; omega))

lemma homFun_invSimplex {n : ℕ} (F : (nerve (WithBot V)).obj (op ⦋n⦌)) :
    homFun (invSimplex F) = F := by
  refine nerve.ext_of_isThin (funext fun i ↦ ?_)
  rw [homFun_obj]
  by_cases h : (i : ℕ) < botCut F
  · rw [toFun_of_lt _ i h, ((lt_botCut_iff F i).1 h)]
  · have hi : (i : ℕ) < n + 1 := i.isLt
    rw [toFun_of_le _ i (not_lt.1 h)]
    refine (congrArg (fun v : V ↦ (↑v : WithBot V))
      (augObj_augMk (invFun F) ⟨i - botCut F, by omega⟩)).trans ?_
    rw [coe_invFun]
    exact congrArg F.obj (Fin.ext (show (i : ℕ) - botCut F + botCut F = i by omega))

lemma homFun_injective {n : ℕ} : Function.Injective (homFun (V := V) (n := n)) :=
  Function.LeftInverse.injective invSimplex_homFun

lemma augObj_augHom_nerveMap {V W : Type u} [Preorder V] [Preorder W] (φ : V →o W)
    {k : ℕ} (y : (nerve V).aug k) (t : Fin k) :
    augObj (augHom (nerveMap φ.monotone.functor) y) t = φ (augObj y t) := by
  cases k with
  | zero => exact t.elim0
  | succ k => rfl

end nerveCone

section ConeNerveIso

open nerveCone

/-- (C3) `Δ[0] ⋆ nerve V ≅ nerve (WithBot V)` for a preorder `V`: the cone point goes to `⊥`
(`conePt_coneNerveIso_hom`) and the base `nerve V` is included via `V ↪ WithBot V`
(`coneι_coneNerveIso_hom`). -/
@[simps]
noncomputable def coneNerveIso (V : Type u) [Preorder V] :
    cone (nerve V) ≅ nerve (WithBot V) where
  hom :=
    { app _ := ↾fun x ↦ homFun x
      naturality _ _ α := ConcreteCategory.hom_ext _ _ fun x ↦ homFun_map α.unop.toOrderHom x }
  inv :=
    { app _ := ↾fun F ↦ invSimplex F
      naturality _ _ α := ConcreteCategory.hom_ext _ _ fun F ↦ homFun_injective (by
        change homFun (invSimplex ((nerve (WithBot V)).map α F)) =
          homFun ((invSimplex F).map α.unop.toOrderHom)
        rw [homFun_invSimplex, homFun_map, homFun_invSimplex]
        rfl) }
  hom_inv_id := NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun x ↦
    invSimplex_homFun x)
  inv_hom_id := NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun F ↦
    homFun_invSimplex F)

lemma conePt_coneNerveIso_hom (V : Type u) [Preorder V] :
    conePt (nerve V) ≫ (coneNerveIso V).hom = const (ComposableArrows.mk₀ (⊥ : WithBot V)) := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun t ↦ ?_)
  refine nerve.ext_of_isThin (funext fun i ↦ ?_)
  change toFun (ConeSimplex.pt (nerve V) n.unop.len) i = ⊥
  exact toFun_of_lt _ i i.isLt

lemma coneι_coneNerveIso_hom (V : Type u) [Preorder V] :
    coneι (nerve V) ≫ (coneNerveIso V).hom =
      nerveMap (WithBot.coe_mono (α := V)).functor := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun y ↦ ?_)
  refine nerve.ext_of_isThin (funext fun i ↦ ?_)
  change toFun (ConeSimplex.ofSimplex y) i = ↑(y.obj i)
  rw [toFun_of_le _ i (Nat.zero_le _)]
  exact congrArg (fun t ↦ (↑(y.obj t) : WithBot V)) (Fin.ext (Nat.sub_zero _))

/-- (C3) is natural in `V`. -/
lemma coneNerveIso_hom_naturality {V W : Type u} [Preorder V] [Preorder W] (φ : V →o W) :
    coneMap (nerveMap φ.monotone.functor) ≫ (coneNerveIso W).hom =
      (coneNerveIso V).hom ≫ nerveMap φ.withBotMap.monotone.functor := by
  refine NatTrans.ext (funext fun n ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_)
  obtain ⟨j, k, hjk, y⟩ := x
  refine nerve.ext_of_isThin (funext fun i ↦ ?_)
  change toFun ⟨j, k, hjk, augHom (nerveMap φ.monotone.functor) y⟩ i =
    φ.withBotMap (toFun ⟨j, k, hjk, y⟩ i)
  by_cases h : (i : ℕ) < j
  · rw [toFun_of_lt _ i h, toFun_of_lt _ i h]
    rfl
  · rw [toFun_of_le _ i (not_lt.1 h), toFun_of_le _ i (not_lt.1 h)]
    exact congrArg (fun v : W ↦ (↑v : WithBot W)) (augObj_augHom_nerveMap φ y _)

end ConeNerveIso

end SSet
