/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Join.Cone

/-!
# The join `A ⋆ B` of two simplicial sets

Kerodon Tag 016Y (Construction 4.3.3.13) / [Lur09, §1.2.8]: an `n`-simplex of `A ⋆ B` is a
decomposition of the vertices `⦋n⦌` into an initial segment of `j` vertices and a final segment
of `k` vertices (`j + k = n + 1`), together with a `(j-1)`-simplex of `A` and a `(k-1)`-simplex
of `B` — that is, a simplex of the *augmented* simplicial set `A⁺` in degree `j` and one of `B⁺`
in degree `k`, in the notation of `Join/Cone.lean`.

This generalises the cone `Δ[0] ⋆ K` of `Join/Cone.lean`, which is the case `A = Δ[0]`
(there the left-hand simplex carries no information and only the number `j` is recorded). The
combinatorial input — `SSet.aug`, `SSet.augMap`, `SSet.cut`, `SSet.residual` — is taken over
verbatim from that file; the one new ingredient is the left-hand analogue of `residual`:

* `SSet.initialSeg α j : Fin (cut α j) →o Fin j`, the restriction of `α` to the vertices it
  sends into the initial segment `Fin j`, with `initialSeg_apply_val`, `initialSeg_id_val` and
  `initialSeg_comp_val`.

The join itself:

* `SSet.JoinSimplex A B n`, with `map`, `map_id`, `map_comp`, and `mapHom` for a pair of
  morphisms; `SSet.join A B : SSet`.
* `SSet.joinMap f g : join A B ⟶ join A' B'`, with `joinMap_id` and `joinMap_comp`; the
  bifunctor `SSet.joinFunctor`; the join of two isomorphisms `SSet.joinMapIso`.
* the two inclusions `SSet.joinInl : A ⟶ join A B` (the simplices with `k = 0`) and
  `SSet.joinInr : B ⟶ join A B` (those with `j = 0`), with their naturality.

Why this is wanted: Kerodon's proof of the special outer horn theorem (Tag 019F,
`SSet.fillOuterHornOfIsEquiv` in `Horn/OuterHorn.lean`, re-exported as
`SSet.HTT.fill_outerHorn_of_isEquiv`) goes through Proposition 4.4.2.13 (Tag 01H0), which
rewrites the outer horn `Λ[n, n]` as a pushout inside the join `Δ[n-2] ⋆ Δ[1] ≅ Δ[n]`
(Lemma 4.3.6.16) and then argues in coslices `C_{f/}` for a *simplex* `f`. Both constructions
need the join for a left-hand factor more general than a point. The conservativity step of that
proof is in `Fibration/Conservative.lean` (Kerodon 019K).
-/

universe u

open CategoryTheory Opposite Simplicial

namespace SSet

/-! ### The initial part of a monotone map -/

/-- The restriction of `α` to the vertices it sends into the initial segment `Fin j`. By
`SSet.lt_cut_iff` these vertices are exactly `Fin (cut α j)`, so this is the left-hand
counterpart of `SSet.residual`. -/
def initialSeg {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (j : ℕ) :
    Fin (cut α j) →o Fin j where
  toFun i := ⟨(α ⟨i, by have := i.isLt; have := cut_le α j; omega⟩ : ℕ),
    (lt_cut_iff α j _).1 i.isLt⟩
  monotone' i i' h := by
    have h' : (α ⟨(i : ℕ), by have := i.isLt; have := cut_le α j; omega⟩ : ℕ) ≤
        (α ⟨(i' : ℕ), by have := i'.isLt; have := cut_le α j; omega⟩ : ℕ) :=
      α.monotone (Fin.mk_le_mk.2 h)
    exact h'

lemma initialSeg_apply_val {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (j : ℕ)
    (i : Fin (cut α j)) :
    (initialSeg α j i : ℕ) = α ⟨i, by have := i.isLt; have := cut_le α j; omega⟩ := rfl

/-- The initial part of the identity is the identity. -/
lemma initialSeg_id_val {m : ℕ} (j : ℕ)
    (i : Fin (cut (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) j)) :
    (initialSeg (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) j i : ℕ) = (i : ℕ) := rfl

/-- The initial part of a composite is the composite of the initial parts. -/
lemma initialSeg_comp_val {l m n : ℕ} (α : Fin (l + 1) →o Fin (m + 1))
    (β : Fin (m + 1) →o Fin (n + 1)) (j : ℕ) (i : Fin (cut (β.comp α) j))
    (i' : Fin (cut α (cut β j))) (hi : (i : ℕ) = i') :
    (initialSeg (β.comp α) j i : ℕ) =
      initialSeg β j (initialSeg α (cut β j) i') := by
  rw [initialSeg_apply_val, initialSeg_apply_val]
  exact congrArg (fun t : Fin (l + 1) ↦ (β (α t) : ℕ)) (Fin.ext hi)

/-- The initial part of `α` at the top cut `n + 1` is `α` itself. -/
lemma initialSeg_top_val {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (i : Fin (cut α (n + 1))) (i' : Fin (m + 1)) (hi : (i : ℕ) = i') :
    (initialSeg α (n + 1) i : ℕ) = α i' :=
  congrArg (fun t : Fin (m + 1) ↦ (α t : ℕ)) (Fin.ext hi)

/-! ### Simplices of the join -/

/-- An `n`-simplex of `A ⋆ B`: an initial block of `j` vertices carrying a simplex of `A⁺` in
degree `j`, and a final block of `k` vertices carrying a simplex of `B⁺` in degree `k`, with
`j + k = n + 1`. -/
structure JoinSimplex (A B : SSet.{u}) (n : ℕ) where
  /-- the number of vertices in the `A`-block -/
  j : ℕ
  /-- the number of vertices in the `B`-block -/
  k : ℕ
  hjk : j + k = n + 1
  /-- the simplex of `A⁺` on the initial block -/
  x : A.aug j
  /-- the simplex of `B⁺` on the final block -/
  y : B.aug k

namespace JoinSimplex

variable {A B : SSet.{u}}

lemma ext_of_j_eq {n : ℕ} {s s' : JoinSimplex A B n} (hj : s.j = s'.j) (hx : HEq s.x s'.x)
    (hy : HEq s.y s'.y) : s = s' := by
  obtain ⟨j, k, hjk, x, y⟩ := s
  obtain ⟨j', k', hjk', x', y'⟩ := s'
  dsimp only at hj hx hy
  subst hj
  obtain rfl : k = k' := by omega
  rw [eq_of_heq hx, eq_of_heq hy]

/-- The action of a simplicial operator. -/
def map {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (s : JoinSimplex A B n) :
    JoinSimplex A B m where
  j := cut α s.j
  k := m + 1 - cut α s.j
  hjk := by have := cut_le α s.j; omega
  x := A.augMap (initialSeg α s.j) s.x
  y := B.augMap (residual α s.j s.k s.hjk) s.y

@[simp] lemma map_j {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (s : JoinSimplex A B n) :
    (s.map α).j = cut α s.j := rfl

@[simp] lemma map_k {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (s : JoinSimplex A B n) :
    (s.map α).k = m + 1 - cut α s.j := rfl

lemma map_id {n : ℕ} (s : JoinSimplex A B n) : s.map OrderHom.id = s := by
  have hj : s.j ≤ n + 1 := by have := s.hjk; omega
  refine ext_of_j_eq (cut_id s.j hj) ?_ ?_
  · refine HEq.trans (augMap_congr A (a' := s.j) (cut_id s.j hj)
      (initialSeg OrderHom.id s.j) OrderHom.id (fun i ↦ initialSeg_id_val s.j i) s.x)
      (heq_of_eq (augMap_id A _ _))
  · refine HEq.trans (augMap_congr B (a' := s.k) (by rw [cut_id s.j hj]; have := s.hjk; omega)
      (residual OrderHom.id s.j s.k s.hjk) OrderHom.id (fun i ↦ ?_) s.y)
      (heq_of_eq (augMap_id B _ _))
    rw [residual_apply_val]
    show ((⟨i + cut OrderHom.id s.j, _⟩ : Fin (n + 1)) : ℕ) - s.j = (i : ℕ)
    dsimp only
    have := cut_id s.j hj
    omega

lemma map_comp {l m n : ℕ} (α : Fin (l + 1) →o Fin (m + 1)) (β : Fin (m + 1) →o Fin (n + 1))
    (s : JoinSimplex A B n) : s.map (β.comp α) = (s.map β).map α := by
  refine ext_of_j_eq (cut_comp α β s.j) ?_ ?_
  · show HEq (A.augMap (initialSeg (β.comp α) s.j) s.x)
      (A.augMap (initialSeg α (cut β s.j)) (A.augMap (initialSeg β s.j) s.x))
    rw [← augMap_comp]
    exact augMap_congr A (by rw [cut_comp]) _ _
      (fun i ↦ initialSeg_comp_val α β s.j i _ rfl) s.x
  · show HEq (B.augMap (residual (β.comp α) s.j s.k s.hjk) s.y)
      (B.augMap (residual α (cut β s.j) (m + 1 - cut β s.j) (s.map β).hjk)
        (B.augMap (residual β s.j s.k s.hjk) s.y))
    rw [← augMap_comp]
    exact augMap_congr B (by rw [cut_comp]) _ _
      (fun i ↦ residual_comp_val α β s.j s.k s.hjk i _ rfl) s.y

/-- The image of a simplex under a pair of morphisms. -/
def mapHom {A' B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') {n : ℕ} (s : JoinSimplex A B n) :
    JoinSimplex A' B' n :=
  ⟨s.j, s.k, s.hjk, augHom f s.x, augHom g s.y⟩

lemma mapHom_map {A' B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : JoinSimplex A B n) :
    (s.map α).mapHom f g = (s.mapHom f g).map α := by
  refine ext_of_j_eq rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · exact augHom_augMap f _ s.x
  · exact augHom_augMap g _ s.y

lemma mapHom_id {n : ℕ} (s : JoinSimplex A B n) : s.mapHom (𝟙 A) (𝟙 B) = s := by
  refine ext_of_j_eq rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · exact augHom_id s.x
  · exact augHom_id s.y

lemma mapHom_comp {A' B' A'' B'' : SSet.{u}} (f : A ⟶ A') (f' : A' ⟶ A'') (g : B ⟶ B')
    (g' : B' ⟶ B'') {n : ℕ} (s : JoinSimplex A B n) :
    s.mapHom (f ≫ f') (g ≫ g') = (s.mapHom f g).mapHom f' g' := by
  refine ext_of_j_eq rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · exact augHom_comp f f' s.x
  · exact augHom_comp g g' s.y

/-! #### The two blocks -/

/-- The simplex of `A ⋆ B` underlying a simplex of `A` (no vertex in the `B`-block). -/
def inl {n : ℕ} (x : A _⦋n⦌) : JoinSimplex A B n := ⟨n + 1, 0, rfl, x, PUnit.unit⟩

/-- The simplex of `A ⋆ B` underlying a simplex of `B` (no vertex in the `A`-block). -/
def inr {n : ℕ} (y : B _⦋n⦌) : JoinSimplex A B n := ⟨0, n + 1, Nat.zero_add _, PUnit.unit, y⟩

lemma inl_map {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (x : A _⦋n⦌) :
    (inl (B := B) x).map α = inl (A.map (SimplexCategory.mkHom α).op x) := by
  refine ext_of_j_eq (cut_top _) ?_ ?_
  · refine HEq.trans (augMap_congr A (a' := m + 1) (cut_top α) _ α
      (fun i ↦ initialSeg_top_val α i _ rfl) x) ?_
    exact heq_of_eq rfl
  · refine HEq.trans (augMap_congr B (a' := 0)
      (by change m + 1 - cut α (n + 1) = 0; have := cut_top α; omega) _ OrderHom.id
      (fun i ↦ absurd i.isLt (by
        have := cut_top α
        change ¬ ((i : ℕ) < m + 1 - cut α (n + 1)); omega)) PUnit.unit) ?_
    exact heq_of_eq rfl

lemma inr_map {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (y : B _⦋n⦌) :
    (inr (A := A) y).map α = inr (B.map (SimplexCategory.mkHom α).op y) := by
  refine ext_of_j_eq (cut_zero _) ?_ ?_
  · refine HEq.trans (augMap_congr A (a' := 0) (cut_zero α) _ OrderHom.id
      (fun i ↦ absurd i.isLt (by have := cut_zero α; omega)) PUnit.unit) ?_
    exact heq_of_eq rfl
  · refine HEq.trans (augMap_congr B (a' := m + 1) (by rw [cut_zero]; rfl) _ α
      (fun i ↦ residual_zero_val _ _ _ i _ rfl) y) ?_
    exact heq_of_eq rfl

lemma inl_mapHom {A' B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') {n : ℕ} (x : A _⦋n⦌) :
    (inl (B := B) x).mapHom f g = inl (f.app _ x) := rfl

lemma inr_mapHom {A' B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') {n : ℕ} (y : B _⦋n⦌) :
    (inr (A := A) y).mapHom f g = inr (g.app _ y) := rfl

end JoinSimplex

/-! ### The join as a simplicial set -/

/-- The join `A ⋆ B` (Kerodon 016Y). -/
def join (A B : SSet.{u}) : SSet.{u} where
  obj n := JoinSimplex A B n.unop.len
  map α := ↾fun s ↦ s.map α.unop.toOrderHom
  map_id _ := ConcreteCategory.hom_ext _ _ fun s ↦ JoinSimplex.map_id s
  map_comp _ _ := ConcreteCategory.hom_ext _ _ fun s ↦ JoinSimplex.map_comp _ _ s

@[simp]
lemma join_map_apply (A B : SSet.{u}) {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (s : (join A B).obj m) : (join A B).map α s = s.map α.unop.toOrderHom := rfl

/-- The join of two morphisms. -/
@[simps]
def joinMap {A B A' B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') : join A B ⟶ join A' B' where
  app _ := ↾fun s ↦ s.mapHom f g
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun s ↦ JoinSimplex.mapHom_map f g _ s

@[simp]
lemma joinMap_id (A B : SSet.{u}) : joinMap (𝟙 A) (𝟙 B) = 𝟙 (join A B) := by
  ext _ s
  exact JoinSimplex.mapHom_id s

@[simp]
lemma joinMap_comp {A B A' B' A'' B'' : SSet.{u}} (f : A ⟶ A') (f' : A' ⟶ A'')
    (g : B ⟶ B') (g' : B' ⟶ B'') :
    joinMap (f ≫ f') (g ≫ g') = joinMap f g ≫ joinMap f' g' := by
  ext _ s
  exact JoinSimplex.mapHom_comp f f' g g' s

/-- The join of two isomorphisms. -/
@[simps]
def joinMapIso {A A' B B' : SSet.{u}} (e : A ≅ A') (e' : B ≅ B') : join A B ≅ join A' B' where
  hom := joinMap e.hom e'.hom
  inv := joinMap e.inv e'.inv
  hom_inv_id := by rw [← joinMap_comp, e.hom_inv_id, e'.hom_inv_id, joinMap_id]
  inv_hom_id := by rw [← joinMap_comp, e.inv_hom_id, e'.inv_hom_id, joinMap_id]

/-- The join bifunctor `(−) ⋆ (−) : SSet × SSet ⥤ SSet`. -/
@[simps]
def joinFunctor : SSet.{u} × SSet.{u} ⥤ SSet.{u} where
  obj AB := join AB.1 AB.2
  map f := joinMap f.1 f.2
  map_id _ := joinMap_id _ _
  map_comp _ _ := joinMap_comp _ _ _ _

/-- The inclusion `A = A ⋆ ∅ ⟶ A ⋆ B`: the simplices with `k = 0`. -/
@[simps]
def joinInl (A B : SSet.{u}) : A ⟶ join A B where
  app _ := ↾fun x ↦ JoinSimplex.inl x
  naturality _ _ α := ConcreteCategory.hom_ext _ _ fun x ↦
    (JoinSimplex.inl_map α.unop.toOrderHom x).symm

/-- The inclusion `B = ∅ ⋆ B ⟶ A ⋆ B`: the simplices with `j = 0`. -/
@[simps]
def joinInr (A B : SSet.{u}) : B ⟶ join A B where
  app _ := ↾fun y ↦ JoinSimplex.inr y
  naturality _ _ α := ConcreteCategory.hom_ext _ _ fun y ↦
    (JoinSimplex.inr_map α.unop.toOrderHom y).symm

lemma joinInl_naturality {A B A' B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    f ≫ joinInl A' B' = joinInl A B ≫ joinMap f g := rfl

lemma joinInr_naturality {A B A' B' : SSet.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    g ≫ joinInr A' B' = joinInr A B ≫ joinMap f g := rfl

end SSet
