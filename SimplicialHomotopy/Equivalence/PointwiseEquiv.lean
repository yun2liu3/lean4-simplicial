/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Horn.ProductCell
import SimplicialHomotopy.Equivalence.FiberHoKan
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Natural equivalences are detected pointwise

**Kerodon Tag 01DK** (Theorem 4.4.4.4) / [Lur09, Proposition 3.1.2.1]: a natural transformation
`g : F → G` between functors `K ⟶ C` into an ∞-category `C`, i.e. an edge of `Fun(K, C)`, is an
equivalence as soon as each component `g(k) : F(k) → G(k)`, `k` a vertex of `K`, is an
equivalence of `C`. This is the statement `SSet.IsEquivOfPointwise` of
`Equivalence/FiberHoKan.lean`; `Cofinal/HTT.lean` re-exports the theorem as
`SSet.HTT.isEquiv_of_pointwise`.

## Proof

Following Kerodon (Theorem 4.4.4.4 via Proposition 4.4.4.9, Tag 023A, with `S = Δ[0]`), the
statement is reduced to a horn-filling property: an outer horn `u : Λ[n+2, 0] ⟶ Fun(K, C)`
whose initial edge is an equivalence at every vertex of `K` extends to `Δ[n+2]`
(`SSet.fill_outerHorn_ihom`). Transposing, `u` is a map `K ⟶ Fun(Λ[n+2, 0], C)` landing in the
subcomplex `SSet.hornEquivSub n C` of simplices whose initial edge is an equivalence at every
vertex, and the claim is that it lifts along the restriction

  `SSet.hornRes' n C : SSet.simplexEquivSub n C ⟶ SSet.hornEquivSub n C`

from the corresponding subcomplex of `Fun(Δ[n+2], C)`. By Mathlib's `SSet.rlp_monomorphisms`,
it suffices to lift against the boundary inclusions `∂Δ[m] ⊆ Δ[m]`
(`SSet.hasLiftingProperty_boundary_hornRes'`); transposed back, such a lifting problem is a map
`Λ[n+2, 0] × Δ[m] ∪ Δ[n+2] × ∂Δ[m] ⟶ C` sending the edges `(0 → 1) × {t}` to equivalences,
which the product cell lemma `SSet.prodStdSimplex.exists_extension_unionProd`
(Kerodon 01DP, `Horn/ProductCell.lean`, resting on Joyal's special outer horn theorem
Kerodon 019F) extends to `Δ[n+2] × Δ[m]`.

Finally, an edge `e` of any simplicial set `D` such that every outer horn `Λ[n+2, 0] ⟶ D` with
initial edge `e` has a filler admits an `InvStruct` (`SSet.Edge.isEquiv_of_fillOuterHorn`,
Kerodon 019F, (2) ⇒ (1)): a `Λ[2, 0]`-filler produces a right inverse `inv` with a `2`-simplex
`α` witnessing `inv ∘ e = id`, and a `Λ[3, 0]`-filler with faces `(•, σ₀ e, σ₁ e, α)` produces
the `2`-simplex witnessing `e ∘ inv = id`.

## Main declarations

* `SSet.Edge.isEquiv_of_fillOuterHorn` : Kerodon 019F, (2) ⇒ (1).
* `SSet.hornEquivSub`, `SSet.simplexEquivSub`, `SSet.hornRes'` : the subcomplexes of
  `Fun(Λ[n+2, 0], C)` and `Fun(Δ[n+2], C)` cut out by the equivalence condition, and the
  restriction between them.
* `SSet.hasLiftingProperty_boundary_hornRes'` : the restriction lifts against `∂Δ[m] ⊆ Δ[m]`.
* `SSet.fill_outerHorn_ihom` : outer horn filling in `Fun(K, C)`.
* `SSet.isEquivOfPointwise : IsEquivOfPointwise` — **Kerodon 01DK**.
-/

universe u

open CategoryTheory Simplicial SimplexCategory Limits Opposite MonoidalCategory MonoidalClosed

namespace SSet

/-! ### Equivalences from outer horn fillers -/

/-- The initial edge of `Λ[2, 0]` is the image of `Δ[1]` under the face `d₂`. -/
lemma horn.edge₀₁_zero_eq :
    horn.edge₀₁.{u} 0 = (horn.ι 0 2 (by decide)).app _ (stdSimplex.objEquiv.symm (𝟙 _)) := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- The initial edge of `Λ[3, 0]` is the image of the edge `0 → 1` of `Δ[2]` under `d₃`. -/
lemma horn.edge₀₁_one_eq :
    horn.edge₀₁.{u} 1 = (horn.ι 0 3 (by decide)).app _ (stdSimplex.edge 2 0 1 (by simp)) := by
  apply Subtype.ext
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- The edge `0 → 1` of `Δ[2]` is the image of `Δ[1]` under the face `d₂`. -/
lemma stdSimplex.edge_two_zero_one_eq :
    stdSimplex.edge.{u} 2 0 1 (by simp) =
      (stdSimplex.δ 2).app _ (stdSimplex.objEquiv.symm (𝟙 _)) := by
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- **Kerodon 019F, (2) ⇒ (1)**: an edge `e` of a simplicial set `D` such that every outer horn
`Λ[n + 2, 0] ⟶ D` with initial edge `e` admits a filler is an equivalence (only `n = 0, 1` are
used). -/
lemma Edge.isEquiv_of_fillOuterHorn {D : SSet.{u}} {x₀ x₁ : D _⦋0⦌} (e : D.Edge x₀ x₁)
    (h : ∀ (n : ℕ) (σ₀ : (Λ[n + 2, 0] : SSet.{u}) ⟶ D), σ₀.app _ (horn.edge₀₁ n) = e.edge →
      ∃ σ : Δ[n + 2] ⟶ D, σ₀ = Λ[n + 2, 0].ι ≫ σ) : e.IsEquiv := by
  -- Step 1: a right inverse `inv` with a `2`-simplex `α` witnessing `inv ∘ e = id`.
  let F : ∀ (j : Fin 3) (_ : j ≠ 0), Δ[1] ⟶ D :=
    fun j _ ↦ if j = 1 then yonedaEquiv.symm (Edge.id x₀).edge else yonedaEquiv.symm e.edge
  have hF : horn.IsCompatible F := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk
    change stdSimplex.δ 1 ≫ yonedaEquiv.symm (Edge.id x₀).edge =
      stdSimplex.δ 1 ≫ yonedaEquiv.symm e.edge
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
      (Edge.id x₀).src_eq, e.src_eq]
  obtain ⟨σ, hσ⟩ := h 0 hF.desc (by
    rw [horn.edge₀₁_zero_eq, ← NatTrans.comp_app_apply, hF.ι_desc]
    simp [F])
  have h2 : D.δ 2 (yonedaEquiv σ) = e.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι (i := 0) (j := 2) (by decide),
      Category.assoc, ← hσ, hF.ι_desc]
    simp [F]
  have h1 : D.δ 1 (yonedaEquiv σ) = (Edge.id x₀).edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι (i := 0) (j := 1) (by decide),
      Category.assoc, ← hσ, hF.ι_desc]
    simp [F]
  let inv : D.Edge x₁ x₀ := Edge.mk (D.δ 0 (yonedaEquiv σ)) (by
      have := D.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) (yonedaEquiv σ)
      simp only [Fin.castSucc_zero, Fin.succ_one_eq_two] at this
      rw [← this, h2, e.tgt_eq]) (by
      have := D.δ_comp_δ_self_apply (i := (0 : Fin 2)) (yonedaEquiv σ)
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at this
      rw [this, h1, (Edge.id x₀).tgt_eq])
  let α : Edge.CompStruct e inv (Edge.id x₀) := Edge.CompStruct.mk (yonedaEquiv σ) h2 rfl h1
  -- Step 2: a `Λ[3, 0]`-filling with faces `(•, σ₀ e, σ₁ e, α)` shows `e ∘ inv = id`.
  let G : ∀ (j : Fin 4) (_ : j ≠ 0), Δ[2] ⟶ D := fun j _ ↦
    if j = 1 then yonedaEquiv.symm (D.σ 0 e.edge)
    else if j = 2 then yonedaEquiv.symm (D.σ 1 e.edge)
    else yonedaEquiv.symm α.simplex
  have hG : horn.IsCompatible G := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk
    · change stdSimplex.δ 1 ≫ yonedaEquiv.symm (D.σ 0 e.edge) =
        stdSimplex.δ 1 ≫ yonedaEquiv.symm (D.σ 1 e.edge)
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
        D.δ_comp_σ_succ'_apply (i := 0) (by decide), D.δ_comp_σ_self'_apply (i := 1) (by decide)]
    · change stdSimplex.δ 2 ≫ yonedaEquiv.symm (D.σ 0 e.edge) =
        stdSimplex.δ 1 ≫ yonedaEquiv.symm α.simplex
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, α.d₁]
      have := D.δ_comp_σ_of_gt_apply (i := (1 : Fin 2)) (j := (0 : Fin 1)) (by decide) e.edge
      rw [show Fin.succ (1 : Fin 2) = 2 by decide, show Fin.castSucc (0 : Fin 1) = 0 by decide,
        e.src_eq] at this
      rw [this]
      rfl
    · change stdSimplex.δ 2 ≫ yonedaEquiv.symm (D.σ 1 e.edge) =
        stdSimplex.δ 2 ≫ yonedaEquiv.symm α.simplex
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, α.d₂,
        D.δ_comp_σ_succ'_apply (i := 1) (by decide)]
  obtain ⟨τ, hτ⟩ := h 1 hG.desc (by
    rw [horn.edge₀₁_one_eq, ← NatTrans.comp_app_apply, hG.ι_desc,
      stdSimplex.edge_two_zero_one_eq, ← NatTrans.comp_app_apply]
    simp [G, stdSimplex.δ_comp_yonedaEquiv_symm, α.d₂])
  have g1 : D.δ 1 (yonedaEquiv τ) = D.σ 0 e.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι (i := 0) (j := 1) (by decide),
      Category.assoc, ← hτ, hG.ι_desc]
    simp [G]
  have g2 : D.δ 2 (yonedaEquiv τ) = D.σ 1 e.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι (i := 0) (j := 2) (by decide),
      Category.assoc, ← hτ, hG.ι_desc]
    simp [G]
  have g3 : D.δ 3 (yonedaEquiv τ) = α.simplex := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι (i := 0) (j := 3) (by decide),
      Category.assoc, ← hτ, hG.ι_desc]
    simp [G]
  refine ⟨⟨inv, α, Edge.CompStruct.mk (D.δ 0 (yonedaEquiv τ)) ?_ ?_ ?_⟩⟩
  · have := D.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) (yonedaEquiv τ)
    rw [show Fin.castSucc (0 : Fin 3) = 0 by decide, show Fin.succ (2 : Fin 3) = 3 by decide]
      at this
    rw [← this, g3, α.d₀]
  · have := D.δ_comp_δ_self_apply (i := (0 : Fin 3)) (yonedaEquiv τ)
    rw [show Fin.castSucc (0 : Fin 3) = 0 by decide, show Fin.succ (0 : Fin 3) = 1 by decide]
      at this
    rw [this, g1, D.δ_comp_σ_self'_apply (i := 0) (by decide)]
  · have := D.δ_comp_δ_apply (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) (yonedaEquiv τ)
    rw [show Fin.castSucc (0 : Fin 3) = 0 by decide, show Fin.succ (1 : Fin 3) = 2 by decide]
      at this
    rw [← this, g2]
    have := D.δ_comp_σ_of_le_apply (i := (0 : Fin 2)) (j := (0 : Fin 1)) (by decide) e.edge
    rw [show Fin.castSucc (0 : Fin 2) = 0 by decide, show Fin.succ (0 : Fin 1) = 1 by decide,
      e.tgt_eq] at this
    rw [this]
    rfl

/-! ### The lifting problem -/

/-- The degenerate edge at a vertex `w` of a simplex `k`, as the image of `k` under the constant
map `⦋1⦌ ⟶ U` at `w`. -/
lemma map_const_one_op {K : SSet.{u}} {U : SimplexCategory} (w : Fin (U.len + 1))
    (k : K.obj (op U)) :
    K.map (SimplexCategory.const ⦋1⦌ U w).op k =
      K.σ 0 (K.map (SimplexCategory.const ⦋0⦌ U w).op k) := by
  rw [SimplicialObject.σ, ← Functor.map_comp_apply, ← op_comp]
  congr 3

/-- The degenerate edge of `Δ[m]` at `t` is the image of the generic simplex under the constant
map at `t`. -/
lemma stdSimplex.edge_self_eq (m : ℕ) (t : Fin (m + 1)) : stdSimplex.edge m t t le_rfl =
    Δ[m].map (SimplexCategory.const ⦋1⦌ ⦋m⦌ t).op (stdSimplex.objEquiv.symm (𝟙 _)) := by
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- The subcomplex of `Fun(Λ[n+2, 0], C)` of the simplices whose value on the initial edge
`0 → 1` at every vertex is an equivalence of `C`. -/
def hornEquivSub (n : ℕ) (C : SSet.{u}) :
    ((ihom (Λ[n + 2, 0] : SSet.{u})).obj C).Subcomplex where
  obj U := {T | ∀ v : Fin (U.unop.len + 1),
    (Edge.mk' (T.app (op ⦋1⦌) (SimplexCategory.const ⦋1⦌ U.unop v).op (horn.edge₀₁ n))).IsEquiv}
  map {U V} i := by
    rintro T hT v
    exact (hT (i.unop.toOrderHom v)).ofEq rfl

/-- The subcomplex of `Fun(Δ[n+2], C)` of the simplices whose restriction to `Λ[n+2, 0]` lies in
`hornEquivSub n C`. -/
abbrev simplexEquivSub (n : ℕ) (C : SSet.{u}) : ((ihom Δ[n + 2]).obj C).Subcomplex :=
  (hornEquivSub n C).preimage ((pre Λ[n + 2, 0].ι).app C)

/-- Restriction along `Λ[n+2, 0] ⊆ Δ[n+2]` between the two subcomplexes. -/
abbrev hornRes' (n : ℕ) (C : SSet.{u}) :
    (simplexEquivSub n C : SSet.{u}) ⟶ (hornEquivSub n C : SSet.{u}) :=
  (hornEquivSub n C).fromPreimage ((pre Λ[n + 2, 0].ι).app C)

variable {C : SSet.{u}} [Quasicategory C] (n : ℕ)

/-- The restriction `hornRes' n C` has the right lifting property against `∂Δ[m] ⊆ Δ[m]`: a
transposed lifting problem is a map `Λ[n+2, 0] × Δ[m] ∪ Δ[n+2] × ∂Δ[m] ⟶ C` to which the product
cell lemma applies. -/
lemma hasLiftingProperty_boundary_hornRes' (m : ℕ) :
    HasLiftingProperty ∂Δ[m].ι (hornRes' n C) where
  sq_hasLift {a b} sq := by
    -- the two halves of the transposed problem agree on `Λ[n+2, 0] × ∂Δ[m]`
    have hAB : Λ[n + 2, 0].ι ▷ (∂Δ[m] : SSet.{u}) ≫ uncurry (a ≫ (simplexEquivSub n C).ι) =
        (Λ[n + 2, 0] : SSet.{u}) ◁ ∂Δ[m].ι ≫ uncurry (b ≫ (hornEquivSub n C).ι) := by
      rw [← uncurry_natural_left, ← Category.assoc, ← sq.w, Category.assoc,
        Subcomplex.fromPreimage_ι, ← Category.assoc, uncurry_pre_app]
    -- the edges `(0 → 1) × {t}` go to equivalences because `b` lands in `hornEquivSub`
    have hH₀ : ∀ t, (Edge.mk' (((Subcomplex.unionProd.isPushout Λ[n + 2, 0] ∂Δ[m]).desc _ _
        hAB).app _ (prodStdSimplex.unionProdEdge₀₁ n m t))).IsEquiv := by
      intro t
      have e1 : ((Subcomplex.unionProd.isPushout Λ[n + 2, 0] ∂Δ[m]).desc _ _ hAB).app _
          (prodStdSimplex.unionProdEdge₀₁ n m t) =
          (uncurry (b ≫ (hornEquivSub n C).ι)).app _
            (horn.edge₀₁ n, stdSimplex.edge m t t le_rfl) := by
        conv_rhs => rw [← (Subcomplex.unionProd.isPushout Λ[n + 2, 0] ∂Δ[m]).inr_desc _ _ hAB]
        rfl
      have e2 : (uncurry (b ≫ (hornEquivSub n C).ι)).app _
            (horn.edge₀₁ n, stdSimplex.edge m t t le_rfl) =
          ((b.app _ (stdSimplex.objEquiv.symm (𝟙 _))).1).app (op ⦋1⦌)
            (SimplexCategory.const ⦋1⦌ ⦋m⦌ t).op (horn.edge₀₁ n) := by
        change ihomEval ((b ≫ (hornEquivSub n C).ι).app _ (stdSimplex.edge m t t le_rfl))
          (horn.edge₀₁ n) = _
        rw [stdSimplex.edge_self_eq, app_map_apply, ihomEval_def, ihom_map_app, Category.comp_id]
        rfl
      rw [e1, e2]
      exact (b.app (op ⦋m⦌) (stdSimplex.objEquiv.symm (𝟙 _))).2 t
    obtain ⟨H, hH⟩ := prodStdSimplex.exists_extension_unionProd _ hH₀
    -- the transposed extension restricts to `b` on `Λ[n+2, 0]`
    have hl : curry H ≫ (pre Λ[n + 2, 0].ι).app C = b ≫ (hornEquivSub n C).ι := by
      rw [curry_pre_app, ← Subcomplex.unionProd.ι₂_ι, Category.assoc, hH,
        (Subcomplex.unionProd.isPushout Λ[n + 2, 0] ∂Δ[m]).inr_desc, curry_uncurry]
    have hrange : Subcomplex.range (curry H) ≤ simplexEquivSub n C := by
      rintro U _ ⟨x, rfl⟩
      change ((curry H ≫ (pre Λ[n + 2, 0].ι).app C).app U x) ∈ (hornEquivSub n C).obj U
      rw [hl]
      exact (b.app U x).2
    refine ⟨⟨⟨Subcomplex.lift (curry H) hrange, ?_, ?_⟩⟩⟩
    · rw [← cancel_mono (simplexEquivSub n C).ι, Category.assoc, Subcomplex.lift_ι,
        ← curry_natural_left, ← Subcomplex.unionProd.ι₁_ι, Category.assoc, hH,
        (Subcomplex.unionProd.isPushout Λ[n + 2, 0] ∂Δ[m]).inl_desc, curry_uncurry]
    · rw [← cancel_mono (hornEquivSub n C).ι, Category.assoc, Subcomplex.fromPreimage_ι,
        Subcomplex.lift_ι_assoc, hl]

/-- **Outer horn filling in `Fun(K, C)`**: a horn `Λ[n+2, 0] ⟶ Fun(K, C)` whose initial edge is
an equivalence at every vertex of `K` extends to `Δ[n+2]` (Kerodon 023A with `S = Δ[0]`). -/
theorem fill_outerHorn_ihom {K : SSet.{u}} (u : (Λ[n + 2, 0] : SSet.{u}) ⟶ (ihom K).obj C)
    (hu : ∀ k : K _⦋0⦌, (Edge.mk' (ihomEval (u.app _ (horn.edge₀₁ n)) (K.σ 0 k))).IsEquiv) :
    ∃ σ : Δ[n + 2] ⟶ (ihom K).obj C, u = Λ[n + 2, 0].ι ≫ σ := by
  -- the restriction lifts against every monomorphism
  have hrlp : (MorphismProperty.monomorphisms SSet.{u}).rlp (hornRes' n C) := by
    rw [rlp_monomorphisms]
    rintro _ _ _ ⟨m⟩
    exact hasLiftingProperty_boundary_hornRes' n m
  -- the transposed horn `K ⟶ Fun(Λ[n+2, 0], C)` lands in `hornEquivSub`
  let v : K ⟶ (ihom (Λ[n + 2, 0] : SSet.{u})).obj C := curry ((β_ _ K).hom ≫ uncurry u)
  have hv : ∀ (U : SimplexCategoryᵒᵖ) (k : K.obj U), v.app U k ∈ (hornEquivSub n C).obj U := by
    intro U k w
    refine (hu (K.map (SimplexCategory.const ⦋0⦌ U.unop w).op k)).ofEq ?_
    show ihomEval (u.app _ (horn.edge₀₁ n))
        (K.σ 0 (K.map (SimplexCategory.const ⦋0⦌ U.unop w).op k)) =
      (v.app U k).app (op ⦋1⦌) (SimplexCategory.const ⦋1⦌ U.unop w).op (horn.edge₀₁ n)
    rw [← map_const_one_op]
    rfl
  let v' : K ⟶ (hornEquivSub n C : SSet.{u}) :=
    Subcomplex.lift v (by rintro U _ ⟨k, rfl⟩; exact hv U k)
  -- lift it along `hornRes'` (against the monomorphism `∅ ⟶ K`), and transpose back
  have sq : CommSq (Subcomplex.isInitialBot.to _) (⊥ : K.Subcomplex).ι (hornRes' n C) v' :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  have := hrlp (⊥ : K.Subcomplex).ι (MorphismProperty.monomorphisms.infer_property _)
  have hW : (sq.lift ≫ (simplexEquivSub n C).ι) ≫ (pre Λ[n + 2, 0].ι).app C = v := by
    rw [Category.assoc, ← Subcomplex.fromPreimage_ι, ← Category.assoc, sq.fac_right]
    rfl
  refine ⟨curry ((β_ K Δ[n + 2]).hom ≫ uncurry (sq.lift ≫ (simplexEquivSub n C).ι)), ?_⟩
  rw [← curry_natural_left, ← Category.assoc, BraidedCategory.braiding_naturality_right,
    Category.assoc, ← uncurry_pre_app, hW, uncurry_curry, SymmetricCategory.symmetry_assoc,
    curry_uncurry]

/-- **Kerodon Tag 01DK** (Theorem 4.4.4.4) / [Lur09, Proposition 3.1.2.1]: a natural
transformation between functors `K ⟶ C` into an ∞-category whose components are all
equivalences is an equivalence of `Fun(K, C)`. -/
theorem isEquivOfPointwise : IsEquivOfPointwise.{u} := by
  intro K C _ F G g hg
  refine Edge.isEquiv_of_fillOuterHorn g fun n σ₀ hσ₀ ↦ fill_outerHorn_ihom n σ₀ fun k ↦ ?_
  rw [hσ₀]
  exact (hg k).ofEq rfl

end SSet
