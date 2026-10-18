/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Equivalence.Equivalences

/-!
# The fibers of `C ⟶ N(hC)` are Kan complexes

For a quasicategory `C` and an `n`-simplex `y` of `N(hC)`, the fiber `fiberHo C y` of
`Fun(Δ[n], C) ⟶ Fun(Δ[n], N(hC))` over `y` is a Kan complex.

Route: by `kanComplex_of_isEquiv_edges` (Kerodon 019D, from Joyal's outer
horn theorem `FillOuterHornOfIsEquiv`) it suffices that every edge of
the fiber is an equivalence. An edge of the fiber is an edge `g` of `Fun(Δ[n], C)` lying over the
degenerate edge at `y`; its components at the vertices of `Δ[n]` are edges of `C` lying over
identities of `hC`, hence equivalences (`isEquiv_of_isIso_homMk`); by pointwise detection of
natural equivalences (the statement `IsEquivOfPointwise`, Kerodon 4.4.4.4 / HTT 3.1.2.1, proved
in `Equivalence/PointwiseEquiv.lean`) `g` is an equivalence of `Fun(Δ[n], C)`;
finally the inverse and the two witnessing
`2`-simplices lie in the fiber because `Fun(Δ[n], N(hC))` is the nerve of a category, so an
inverse of a degenerate edge is degenerate (`invStruct_eq_const_of_nerve`).

## Main declarations

* `SSet.ihomEval T a`, `SSet.edgeComponent g k` : evaluation of simplices / edges of `Fun(K, C)`
  at simplices / vertices of `K`.
* `SSet.IsEquivOfPointwise` : the statement "natural equivalences are detected pointwise"
  (proved in `Equivalence/PointwiseEquiv.lean`, re-exported as `HTT.isEquiv_of_pointwise`).
* `SSet.ihom_nerve_ext`, `SSet.invStruct_eq_const_of_nerve` : simplices of `Fun(K, nerve D)` are
  determined by their values on vertices and edges; an inverse of a constant edge is constant.
* `SSet.isEquiv_of_invStruct_fst` : an edge of a fiber over a point whose image in the total
  space has an inverse lying over the point is an equivalence in the fiber.
* `SimplicialHomotopy.kanComplex_fiberHo_of` : the fibers are Kan complexes, from the two
  hypotheses `FillOuterHornOfIsEquiv` and `IsEquivOfPointwise`.
-/

universe u

open CategoryTheory Limits Opposite Simplicial MonoidalCategory MonoidalClosed

namespace SSet

/-! ### Simplices of `Fun(K, X) = (ihom K).obj X` -/

section Ihom

variable {K X Y : SSet.{u}}

/-- The simplicial structure of `Fun(K, X)` acts on a simplex `T` (a `Functor.HomObj`) by
precomposition in the shape variable: `(φ^* T)(ψ, a) = T(φ ≫ ψ, a)`. -/
lemma ihom_map_app {d d' d'' : SimplexCategoryᵒᵖ} (T : ((ihom K).obj X).obj d) (φ : d ⟶ d')
    (ψ : d' ⟶ d'') (a : K.obj d'') :
    (((ihom K).obj X).map φ T).app d'' ψ a = T.app d'' (φ ≫ ψ) a :=
  rfl

/-- Postcomposition `Fun(K, X) ⟶ Fun(K, Y)` acts on values. -/
lemma ihom_map_app_app {d d' : SimplexCategoryᵒᵖ} (f : X ⟶ Y) (T : ((ihom K).obj X).obj d)
    (ψ : d ⟶ d') (a : K.obj d') :
    (((ihom K).map f).app d T).app d' ψ a = f.app d' (T.app d' ψ a) :=
  rfl

/-- Naturality of the values of a simplex of `Fun(K, X)`. -/
lemma ihom_app_map {d d' d'' : SimplexCategoryᵒᵖ} (T : ((ihom K).obj X).obj d) (ψ : d ⟶ d')
    (φ : d' ⟶ d'') (a : K.obj d') :
    X.map φ (T.app d' ψ a) = T.app d'' (ψ ≫ φ) (K.map φ a) :=
  (ConcreteCategory.congr_hom (T.naturality φ ψ) a).symm

/-- A value of `T` at `ψ` is the value of `((ihom K).obj X).map ψ T` at the identity. -/
lemma ihom_app_eq {d d' : SimplexCategoryᵒᵖ} (T : ((ihom K).obj X).obj d) (ψ : d ⟶ d')
    (a : K.obj d') :
    T.app d' ψ a = (((ihom K).obj X).map ψ T).app d' (𝟙 d') a := by
  rw [ihom_map_app, Category.comp_id]

/-- Naturality of a map of simplicial sets, applied to a simplex. -/
lemma app_map_apply (f : K ⟶ X) {d d' : SimplexCategoryᵒᵖ} (φ : d ⟶ d') (a : K.obj d) :
    f.app d' (K.map φ a) = X.map φ (f.app d a) :=
  NatTrans.naturality_apply f φ a

/-- Evaluation of an `m`-simplex of `Fun(K, X)` at an `m`-simplex of `K` ("the diagonal"). -/
def ihomEval {m : ℕ} (T : ((ihom K).obj X) _⦋m⦌) (a : K _⦋m⦌) : X _⦋m⦌ :=
  T.app _ (𝟙 _) a

lemma ihomEval_def {m : ℕ} (T : ((ihom K).obj X) _⦋m⦌) (a : K _⦋m⦌) :
    ihomEval T a = T.app _ (𝟙 _) a :=
  rfl

lemma ihomEval_map {m : ℕ} (f : X ⟶ Y) (T : ((ihom K).obj X) _⦋m⦌) (a : K _⦋m⦌) :
    ihomEval (((ihom K).map f).app _ T) a = f.app _ (ihomEval T a) :=
  rfl

/-- Faces of a diagonal evaluation. -/
lemma δ_ihomEval {m : ℕ} (i : Fin (m + 2)) (T : ((ihom K).obj X) _⦋m + 1⦌) (a : K _⦋m + 1⦌) :
    X.δ i (ihomEval T a) = ihomEval (((ihom K).obj X).δ i T) (K.δ i a) := by
  simp only [ihomEval_def, SimplicialObject.δ_def]
  rw [ihom_app_map, ihom_map_app, Category.id_comp, Category.comp_id]

/-- Degeneracies of a diagonal evaluation. -/
lemma σ_ihomEval {m : ℕ} (i : Fin (m + 1)) (T : ((ihom K).obj X) _⦋m⦌) (a : K _⦋m⦌) :
    X.σ i (ihomEval T a) = ihomEval (((ihom K).obj X).σ i T) (K.σ i a) := by
  simp only [ihomEval_def, SimplicialObject.σ_def]
  rw [ihom_app_map, ihom_map_app, Category.id_comp, Category.comp_id]

/-- Every simplex in the image of `pointOf f : 𝟙_ SSet ⟶ Fun(K, X)` is the constant simplex
`Functor.HomObj.ofNatTrans f`. -/
lemma pointOf_app (f : K ⟶ X) {d : SimplexCategoryᵒᵖ} (u : (𝟙_ SSet.{u}).obj d) :
    (pointOf f).app d u = Functor.HomObj.ofNatTrans f :=
  rfl

/-- The constant simplices are stable under the simplicial operators. -/
lemma map_ofNatTrans (f : K ⟶ X) {d d' : SimplexCategoryᵒᵖ} (φ : d ⟶ d') :
    ((ihom K).obj X).map φ (Functor.HomObj.ofNatTrans f) = Functor.HomObj.ofNatTrans f :=
  rfl

lemma δ_ofNatTrans (f : K ⟶ X) {m : ℕ} (i : Fin (m + 2)) :
    ((ihom K).obj X).δ i (Functor.HomObj.ofNatTrans f (A := coyoneda.obj (op (op ⦋m + 1⦌)))) =
      Functor.HomObj.ofNatTrans f :=
  rfl

lemma σ_ofNatTrans (f : K ⟶ X) {m : ℕ} (i : Fin (m + 1)) :
    ((ihom K).obj X).σ i (Functor.HomObj.ofNatTrans f (A := coyoneda.obj (op (op ⦋m⦌)))) =
      Functor.HomObj.ofNatTrans f :=
  rfl

lemma ihomEval_ofNatTrans (f : K ⟶ X) {m : ℕ} (a : K _⦋m⦌) :
    ihomEval (Functor.HomObj.ofNatTrans f) a = f.app _ a :=
  rfl

/-- The component at a vertex `k` of `K` of an edge `g : F → G` of `Fun(K, X)`: the edge
`F(k) → G(k)` of `X` obtained by evaluating `g` at the degenerate edge of `k`. -/
def edgeComponent {F G : ((ihom K).obj X) _⦋0⦌} (g : ((ihom K).obj X).Edge F G) (k : K _⦋0⦌) :
    X.Edge (ihomEval F k) (ihomEval G k) :=
  Edge.mk (ihomEval g.edge (K.σ 0 k))
    (by rw [δ_ihomEval, g.src_eq, δ_comp_σ_succ'_apply (i := 0) (j := 1) rfl])
    (by rw [δ_ihomEval, g.tgt_eq, δ_comp_σ_self'_apply (i := 0) (j := 0) rfl])

@[simp]
lemma edgeComponent_edge {F G : ((ihom K).obj X) _⦋0⦌} (g : ((ihom K).obj X).Edge F G)
    (k : K _⦋0⦌) : (edgeComponent g k).edge = ihomEval g.edge (K.σ 0 k) :=
  rfl

/-- Components commute with postcomposition. -/
lemma edgeComponent_map_edge {F G : ((ihom K).obj X) _⦋0⦌} (g : ((ihom K).obj X).Edge F G)
    (f : X ⟶ Y) (k : K _⦋0⦌) :
    (edgeComponent (g.map ((ihom K).map f)) k).edge = ((edgeComponent g k).map f).edge :=
  rfl

end Ihom

/-! ### Simplices of `Fun(K, nerve D)` -/

section Nerve

variable {K : SSet.{u}} {D : Type u} [Category.{u} D]

/-- A map `⦋k⦌ ⟶ ⦋m⦌` with `k < m` is not surjective. -/
lemma _root_.SimplexCategory.not_surjective_of_lt {m k : ℕ} (h : k < m) (θ : ⦋k⦌ ⟶ ⦋m⦌) :
    ¬ Function.Surjective θ.toOrderHom := fun hs ↦ by
  have : Epi θ := SimplexCategory.epi_iff_surjective.2 hs
  have := SimplexCategory.le_of_epi θ
  omega

/-- Two simplices of `Fun(K, nerve D)` agreeing on all vertices and edges are equal
(a simplex of a nerve is determined by its spine). -/
lemma ihom_nerve_ext {m : ℕ} {T T' : ((ihom K).obj (nerve D)) _⦋m⦌}
    (h₀ : ∀ (ψ : op ⦋m⦌ ⟶ op ⦋0⦌) (b : K _⦋0⦌), T.app _ ψ b = T'.app _ ψ b)
    (h₁ : ∀ (ψ : op ⦋m⦌ ⟶ op ⦋1⦌) (b : K _⦋1⦌), T.app _ ψ b = T'.app _ ψ b) : T = T' := by
  apply Functor.HomObj.ext
  funext d ψ
  apply ConcreteCategory.hom_ext
  intro b
  obtain ⟨⟨k⟩⟩ := d
  apply (IsStrictSegal.segal (X := nerve D) k).injective
  apply Path.ext
  · funext i
    rw [spine_vertex, spine_vertex, ihom_app_map, ihom_app_map]
    exact h₀ _ _
  · funext i
    rw [spine_arrow, spine_arrow, ihom_app_map, ihom_app_map]
    exact h₁ _ _

/-- If all faces of a simplex `T` of `Fun(K, X)` are the constant simplex of `f`, then the
values of `T` on non-surjective maps are the values of `f`. -/
lemma app_eq_of_δ_eq_const {X : SSet.{u}} (f : K ⟶ X) {m k : ℕ} (T : ((ihom K).obj X) _⦋m + 1⦌)
    (hT : ∀ j, ((ihom K).obj X).δ j T = Functor.HomObj.ofNatTrans f)
    (ψ : op ⦋m + 1⦌ ⟶ op ⦋k⦌) (hψ : ¬ Function.Surjective ψ.unop.toOrderHom) (b : K _⦋k⦌) :
    T.app _ ψ b = f.app _ b := by
  obtain ⟨j, θ, hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective ψ.unop hψ
  have : ψ = (SimplexCategory.δ j).op ≫ θ.op := by
    rw [← op_comp, ← hθ]
    rfl
  rw [this, ← ihom_map_app, ← SimplicialObject.δ_def, hT]
  rfl

/-- In the nerve of a category, a `2`-simplex whose `2`-nd face is degenerate has equal
`0`-th and `1`-st faces. -/
lemma nerve_δ_zero_eq_δ_one {Z : (nerve D) _⦋2⦌} {v : (nerve D) _⦋0⦌}
    (h : (nerve D).δ 2 Z = (nerve D).σ 0 v) : (nerve D).δ 0 Z = (nerve D).δ 1 Z := by
  obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, c, rfl⟩ := Edge.CompStruct.exists_of_simplex Z
  rw [c.d₂] at h
  have h₀ : v = x₀ := by rw [← e₀₁.src_eq, h, δ_comp_σ_succ'_apply (i := 0) (j := 1) rfl]
  have h₁ : v = x₁ := by rw [← e₀₁.tgt_eq, h, δ_comp_σ_self'_apply (i := 0) (j := 0) rfl]
  subst h₀ h₁
  obtain rfl : e₀₁ = Edge.id v := Edge.ext h
  have := nerve.homEquiv_comp c
  have hid : nerve.homEquiv (Edge.id v) = 𝟙 _ := nerve.homEquiv_id v
  rw [hid, Category.id_comp] at this
  rw [c.d₀, c.d₁, nerve.homEquiv.injective this]

/-- `nerve.homEquiv` of a degenerate edge is an isomorphism. -/
lemma isIso_nerve_homEquiv_of_eq_σ {a c : (nerve D) _⦋0⦌} (ed : (nerve D).Edge a c)
    (v : (nerve D) _⦋0⦌) (h : ed.edge = (nerve D).σ 0 v) : IsIso (nerve.homEquiv ed) := by
  have h₀ : v = a := by rw [← ed.src_eq, h, δ_comp_σ_succ'_apply (i := 0) (j := 1) rfl]
  have h₁ : v = c := by rw [← ed.tgt_eq, h, δ_comp_σ_self'_apply (i := 0) (j := 0) rfl]
  subst h₀ h₁
  obtain rfl : ed = Edge.id v := Edge.ext h
  have hid : nerve.homEquiv (Edge.id v) = 𝟙 _ := nerve.homEquiv_id v
  rw [hid]
  infer_instance

/-- **The inverse of a constant edge of `Fun(K, nerve D)` is constant**, and so are the two
`2`-simplices witnessing the inverse identities: `Fun(K, nerve D)` behaves like the nerve of a
category. Here "constant" means the simplex `Functor.HomObj.ofNatTrans f` attached to
`f : K ⟶ nerve D`. -/
lemma invStruct_eq_const_of_nerve (f : K ⟶ nerve D)
    {x₀ x₁ : ((ihom K).obj (nerve D)) _⦋0⦌}
    (hx₀ : x₀ = Functor.HomObj.ofNatTrans f) (hx₁ : x₁ = Functor.HomObj.ofNatTrans f)
    {e : ((ihom K).obj (nerve D)).Edge x₀ x₁} (he : e.edge = Functor.HomObj.ofNatTrans f)
    (I : e.InvStruct) :
    I.inv.edge = Functor.HomObj.ofNatTrans f ∧
      I.homInvId.simplex = Functor.HomObj.ofNatTrans f ∧
      I.invHomId.simplex = Functor.HomObj.ofNatTrans f := by
  have hfaces : ∀ j, ((ihom K).obj (nerve D)).δ j I.inv.edge = Functor.HomObj.ofNatTrans f := by
    intro j
    fin_cases j
    · exact I.inv.tgt_eq.trans hx₀
    · exact I.inv.src_eq.trans hx₁
  have hinv : I.inv.edge = Functor.HomObj.ofNatTrans f := by
    apply ihom_nerve_ext
    · intro ψ b
      exact app_eq_of_δ_eq_const f _ hfaces ψ (SimplexCategory.not_surjective_of_lt (by omega) _) b
    · intro ψ b
      by_cases hs : Function.Surjective ψ.unop.toOrderHom
      · have hψ : ψ = 𝟙 _ := by
          have : Epi ψ.unop := SimplexCategory.epi_iff_surjective.2 hs
          exact Quiver.Hom.unop_inj (SimplexCategory.eq_id_of_epi ψ.unop)
        subst hψ
        change ihomEval I.inv.edge b = f.app _ b
        have h2 : K.δ 2 (K.σ 0 b) = K.σ 0 (K.δ 1 b) :=
          δ_comp_σ_of_gt_apply (i := 1) (j := 0) (by decide) b
        have hσ : ((ihom K).obj (nerve D)).σ 0 x₀ = Functor.HomObj.ofNatTrans f := by
          rw [hx₀]
          exact σ_ofNatTrans f 0
        have hZ := nerve_δ_zero_eq_δ_one (Z := ihomEval I.homInvId.simplex (K.σ 0 b))
          (v := f.app _ (K.δ 1 b)) (by
            rw [δ_ihomEval, I.homInvId.d₂, he, ihomEval_ofNatTrans, h2, SimplicialObject.σ_def,
              SimplicialObject.σ_def, NatTrans.naturality_apply])
        rw [δ_ihomEval, δ_ihomEval, I.homInvId.d₀, I.homInvId.d₁, Edge.id_edge, hσ,
          ihomEval_ofNatTrans, δ_comp_σ_self'_apply (i := 0) (j := 0) rfl,
          δ_comp_σ_succ'_apply (i := 0) (j := 1) rfl] at hZ
        exact hZ
      · exact app_eq_of_δ_eq_const f _ hfaces ψ hs b
  refine ⟨hinv, ?_, ?_⟩
  · have hfaces' : ∀ j, ((ihom K).obj (nerve D)).δ j I.homInvId.simplex =
        Functor.HomObj.ofNatTrans f := by
      intro j
      fin_cases j
      · exact I.homInvId.d₀.trans hinv
      · exact I.homInvId.d₁.trans (by rw [Edge.id_edge, hx₀]; exact σ_ofNatTrans f 0)
      · exact I.homInvId.d₂.trans he
    apply ihom_nerve_ext
    · intro ψ b
      exact app_eq_of_δ_eq_const f _ hfaces' ψ (SimplexCategory.not_surjective_of_lt (by omega) _) b
    · intro ψ b
      exact app_eq_of_δ_eq_const f _ hfaces' ψ (SimplexCategory.not_surjective_of_lt (by omega) _) b
  · have hfaces' : ∀ j, ((ihom K).obj (nerve D)).δ j I.invHomId.simplex =
        Functor.HomObj.ofNatTrans f := by
      intro j
      fin_cases j
      · exact I.invHomId.d₀.trans he
      · exact I.invHomId.d₁.trans (by rw [Edge.id_edge, hx₁]; exact σ_ofNatTrans f 0)
      · exact I.invHomId.d₂.trans hinv
    apply ihom_nerve_ext
    · intro ψ b
      exact app_eq_of_δ_eq_const f _ hfaces' ψ (SimplexCategory.not_surjective_of_lt (by omega) _) b
    · intro ψ b
      exact app_eq_of_δ_eq_const f _ hfaces' ψ (SimplexCategory.not_surjective_of_lt (by omega) _) b

end Nerve

/-! ### Fibers over a point -/

section Pullback

variable {X B : SSet.{u}} (q : X ⟶ B) (b : 𝟙_ SSet.{u} ⟶ B)

/-- Simplices of a pullback over the terminal object are determined by their first
projection. -/
lemma pullback_fst_app_injective_of_unit {m : ℕ} :
    Function.Injective ((pullback.fst q b).app (op ⦋m⦌)) := by
  intro s s' h
  apply yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, h]
  · exact CartesianMonoidalCategory.toUnit_unique _ _

/-- Lift a simplex of `X` lying over the point `b` to the pullback. -/
noncomputable def pullbackUnitSimplex {m : ℕ} (s : X _⦋m⦌)
    (h : ∀ u : (𝟙_ SSet.{u}).obj (op ⦋m⦌), q.app _ s = b.app _ u) :
    (pullback q b) _⦋m⦌ :=
  yonedaEquiv (pullback.lift (yonedaEquiv.symm s) (CartesianMonoidalCategory.toUnit _) (by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, h]))

@[simp]
lemma fst_app_pullbackUnitSimplex {m : ℕ} (s : X _⦋m⦌)
    (h : ∀ u : (𝟙_ SSet.{u}).obj (op ⦋m⦌), q.app _ s = b.app _ u) :
    (pullback.fst q b).app _ (pullbackUnitSimplex q b s h) = s := by
  rw [pullbackUnitSimplex, ← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- An edge `e` of the fiber `pullback q b` whose image in `X` has an inverse (with witnessing
`2`-simplices) lying over the point `b` is an equivalence of the fiber. -/
lemma isEquiv_of_invStruct_fst {x₀ x₁ : (pullback q b) _⦋0⦌} (e : (pullback q b).Edge x₀ x₁)
    (I : (e.map (pullback.fst q b)).InvStruct)
    (h₁ : ∀ u : (𝟙_ SSet.{u}).obj (op ⦋1⦌), q.app _ I.inv.edge = b.app _ u)
    (h₂ : ∀ u : (𝟙_ SSet.{u}).obj (op ⦋2⦌), q.app _ I.homInvId.simplex = b.app _ u)
    (h₃ : ∀ u : (𝟙_ SSet.{u}).obj (op ⦋2⦌), q.app _ I.invHomId.simplex = b.app _ u) :
    e.IsEquiv := by
  let inv : (pullback q b).Edge x₁ x₀ := Edge.mk (pullbackUnitSimplex q b _ h₁)
    (pullback_fst_app_injective_of_unit q b
      (by rw [δ_naturality_apply, fst_app_pullbackUnitSimplex, I.inv.src_eq]))
    (pullback_fst_app_injective_of_unit q b
      (by rw [δ_naturality_apply, fst_app_pullbackUnitSimplex, I.inv.tgt_eq]))
  have hinv : (pullback.fst q b).app _ inv.edge = I.inv.edge := fst_app_pullbackUnitSimplex q b _ h₁
  refine ⟨⟨inv, Edge.CompStruct.mk (pullbackUnitSimplex q b _ h₂) ?_ ?_ ?_,
    Edge.CompStruct.mk (pullbackUnitSimplex q b _ h₃) ?_ ?_ ?_⟩⟩
  · refine pullback_fst_app_injective_of_unit q b ?_
    rw [δ_naturality_apply, fst_app_pullbackUnitSimplex, I.homInvId.d₂, Edge.map_edge]
  · refine pullback_fst_app_injective_of_unit q b ?_
    rw [δ_naturality_apply, fst_app_pullbackUnitSimplex, I.homInvId.d₀, hinv]
  · refine pullback_fst_app_injective_of_unit q b ?_
    rw [δ_naturality_apply, fst_app_pullbackUnitSimplex, I.homInvId.d₁, Edge.id_edge,
      Edge.id_edge, σ_naturality_apply]
  · refine pullback_fst_app_injective_of_unit q b ?_
    rw [δ_naturality_apply, fst_app_pullbackUnitSimplex, I.invHomId.d₂, hinv]
  · refine pullback_fst_app_injective_of_unit q b ?_
    rw [δ_naturality_apply, fst_app_pullbackUnitSimplex, I.invHomId.d₀, Edge.map_edge]
  · refine pullback_fst_app_injective_of_unit q b ?_
    rw [δ_naturality_apply, fst_app_pullbackUnitSimplex, I.invHomId.d₁, Edge.id_edge,
      Edge.id_edge, σ_naturality_apply]

end Pullback

/-! ### Pointwise detection of natural equivalences (statement) -/

/-- The statement of Kerodon Theorem 4.4.4.4 (Tag 01DK) / [Lur09, Proposition 3.1.2.1]: a natural
transformation `g : F → G` between maps `K ⟶ C` into a quasicategory, i.e. an edge of
`Fun(K, C) = (ihom K).obj C`, is an equivalence as soon as each of its components
`edgeComponent g k : F(k) → G(k)` (evaluation at the degenerate edge of the vertex `k`) is
an equivalence of `C`. Proved in `Equivalence/PointwiseEquiv.lean` (`SSet.isEquivOfPointwise`,
re-exported as `HTT.isEquiv_of_pointwise`). -/
def IsEquivOfPointwise : Prop :=
  ∀ {K C : SSet.{u}} [Quasicategory C] {F G : ((ihom K).obj C) _⦋0⦌}
    (g : ((ihom K).obj C).Edge F G), (∀ k : K _⦋0⦌, (edgeComponent g k).IsEquiv) → g.IsEquiv

end SSet

namespace SimplicialHomotopy

open SSet SSet.HomotopyCategory

variable (C : SSet.{u}) [Quasicategory C]

omit [Quasicategory C] in
/-- An edge of `C` whose image in `N(hC)` is degenerate is an isomorphism in `hC`. -/
lemma isIso_homMk_of_map_toNerveHo_eq_σ {x y : C _⦋0⦌} (e : C.Edge x y)
    (v : (nerve C.HomotopyCategory) _⦋0⦌)
    (h : (e.map (toNerveHo C)).edge = (nerve C.HomotopyCategory).σ 0 v) : IsIso (homMk e) := by
  rw [← homEquiv_edge_map_toNerveHo C e]
  have := isIso_nerve_homEquiv_of_eq_σ (e.map (toNerveHo C)) v h
  infer_instance

/-- The fiber of `Fun(K, C) ⟶ Fun(K, N(hC))` over the point `f : K ⟶ N(hC)` is a Kan
complex. -/
theorem kanComplex_pullback_toNerveHo_of (H₁ : FillOuterHornOfIsEquiv.{u})
    (H₂ : IsEquivOfPointwise.{u}) {K : SSet.{u}} (f : K ⟶ nerve C.HomotopyCategory)
    (hQ : Quasicategory (pullback ((ihom K).map (toNerveHo C)) (pointOf f))) :
    KanComplex (pullback ((ihom K).map (toNerveHo C)) (pointOf f)) := by
  have := hQ
  refine SSet.kanComplex_of_isEquiv_edges _ ?_ H₁
  intro x₀ x₁ e
  have q_fst : ∀ {d : SimplexCategoryᵒᵖ}
      (z : (pullback ((ihom K).map (toNerveHo C)) (pointOf f)).obj d),
      ((ihom K).map (toNerveHo C)).app d
          ((pullback.fst ((ihom K).map (toNerveHo C)) (pointOf f)).app d z) =
        Functor.HomObj.ofNatTrans f := by
    intro d z
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (pullback.condition (f := (ihom K).map (toNerveHo C)) (g := pointOf f)) d) z
    exact h.trans (pointOf_app f _)
  have hcomp : ∀ k : K _⦋0⦌,
      (edgeComponent
        (e.map (pullback.fst ((ihom K).map (toNerveHo C)) (pointOf f))) k).IsEquiv := by
    intro k
    have hσ : ((edgeComponent
          (e.map (pullback.fst ((ihom K).map (toNerveHo C)) (pointOf f))) k).map
          (toNerveHo C)).edge =
        (nerve C.HomotopyCategory).σ 0 (f.app _ k) := by
      rw [Edge.map_edge, edgeComponent_edge, ← ihomEval_map, Edge.map_edge, q_fst,
        ihomEval_ofNatTrans, σ_naturality_apply]
    have := isIso_homMk_of_map_toNerveHo_eq_σ C _ _ hσ
    exact isEquiv_of_isIso_homMk _
  obtain ⟨I⟩ := H₂ _ hcomp
  have hI := invStruct_eq_const_of_nerve f (q_fst x₀) (q_fst x₁)
    (e := (e.map (pullback.fst ((ihom K).map (toNerveHo C)) (pointOf f))).map
      ((ihom K).map (toNerveHo C))) (q_fst _)
    (I.map ((ihom K).map (toNerveHo C)))
  obtain ⟨h₁, h₂, h₃⟩ := hI
  -- the three equations are, definitionally, about the images under `(ihom K).map (toNerveHo C)`
  exact isEquiv_of_invStruct_fst _ _ e I (fun u ↦ h₁.trans (pointOf_app f u).symm)
    (fun u ↦ h₂.trans (pointOf_app f u).symm) (fun u ↦ h₃.trans (pointOf_app f u).symm)

/-- For a quasicategory `C` and an `n`-simplex `y` of
`N(hC)`, the fiber `fiberHo C y` of `Fun(Δ[n], C) ⟶ Fun(Δ[n], N(hC))` over `y` is a Kan
complex, given Joyal's outer horn theorem and pointwise detection of natural equivalences as
hypotheses. Both are theorems: `SSet.fillOuterHornOfIsEquiv` in `Horn/OuterHorn.lean` and
`SSet.isEquivOfPointwise` in `Equivalence/PointwiseEquiv.lean`, which imports this file. -/
theorem kanComplex_fiberHo_of (H₁ : FillOuterHornOfIsEquiv.{u}) (H₂ : IsEquivOfPointwise.{u})
    {n : ℕ} (y : (nerve C.HomotopyCategory) _⦋n⦌) : KanComplex (fiberHo C y) :=
  kanComplex_pullback_toNerveHo_of C H₁ H₂ (yonedaEquiv.symm y) (quasicategory_fiberHo C y)

end SimplicialHomotopy
