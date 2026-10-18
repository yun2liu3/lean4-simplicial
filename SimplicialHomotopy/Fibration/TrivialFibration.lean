/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Fibration.Fiber
import SimplicialHomotopy.Anodyne.CellLifting
import SimplicialHomotopy.Anodyne.Deformation
import SimplicialHomotopy.Equivalence.WeakEquivalenceKan
import SimplicialHomotopy.Horn.OuterHorn
import SimplicialHomotopy.Nerve.InnerFibrationToNerve
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Right fibrations with weakly contractible fibers are trivial fibrations

A right fibration `q : E ⟶ B` all of whose fibers `fiber q b` are weakly contractible has the
right lifting property against all monomorphisms of simplicial sets ([Lur09, 2.1.3.4] in the
right-fibration flavour; Kerodon 4.4.2), the last analytic input of Joyal's Theorem A.

The proof reduces (via `SSet.rlp_monomorphisms`) to lifting against the boundary inclusions
`∂Δ[n] ⟶ Δ[n]`, and then, pulling back along `Δ[n] ⟶ B`, to the case of a right fibration
`q : E ⟶ Δ[n]` with weakly contractible fibers, where one must produce a section on `Δ[n]`
extending a given section on `∂Δ[n]`. This is done with the *prism contraction*
`H : Δ[1] ⊗ Δ[n] ⟶ Δ[n]`, `(t, x) ↦ (l ↦ if t l = 1 then x l else 0)`, which is the identity
at time `1` and constant at the vertex `0` at time `0`:

1. the given section `a : ∂Δ[n] ⟶ E` is deformed along `H` to time `0` using the right
   anodyne extension `{1} ⊗ ∂Δ[n] ⟶ Δ[1] ⊗ ∂Δ[n]`;
2. at time `0` the deformed map lands in the fiber over the vertex `0`, which is a weakly
   contractible Kan complex, so it extends over `Δ[n]`;
3. the two pieces glue to `Λ[1, 0].unionProd ∂Δ[n] ⟶ E` over `H`, and the cell-by-cell lifting
   theorem `exists_lift_of_rightFibration` for the standard pairing of
   `Λ[1, 0].unionProd ∂Δ[n] ⊆ Δ[1] ⊗ Δ[n]` extends it to `Δ[1] ⊗ Δ[n]`; the only cells where a
   genuine (outer) horn filling is needed are the index-`0` cells, whose image under `H` is
   degenerate at the vertex `0` along the edge `0 → 1`, so that the edge to be filled lies in a
   fiber, hence is an equivalence, and `fillOuterHornOfIsEquiv` applies.

Restricting the resulting lift to time `1` gives the section.

## Main declarations

* `SSet.prismContraction n : Δ[1] ⊗ Δ[n] ⟶ Δ[n]`.
* `SSet.exists_section_of_rightFibration_stdSimplex`: the boundary-extension statement over
  `Δ[n]`.
* `SSet.rlp_monomorphisms_of_rightFibration_of_weaklyContractible_fibers`: the main theorem.
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial Opposite

namespace SSet

/-! ### The prism contraction of a standard simplex onto its vertex `0` -/

/-- The monotone map `l ↦ if t l = 1 then x l else 0` underlying `prismContraction`. -/
def prismContractionOrderHom {m n : ℕ} (t : Fin (m + 1) →o Fin 2)
    (x : Fin (m + 1) →o Fin (n + 1)) : Fin (m + 1) →o Fin (n + 1) where
  toFun l := if t l = 1 then x l else 0
  monotone' l l' hll' := by
    dsimp only
    split_ifs with h h'
    · exact x.monotone hll'
    · exact (h' (le_antisymm (Fin.le_last _) (h ▸ t.monotone hll'))).elim
    · exact Fin.zero_le _
    · exact le_rfl

@[simp]
lemma prismContractionOrderHom_apply {m n : ℕ} (t : Fin (m + 1) →o Fin 2)
    (x : Fin (m + 1) →o Fin (n + 1)) (l : Fin (m + 1)) :
    prismContractionOrderHom t x l = if t l = 1 then x l else 0 := rfl

/-- The contraction `Δ[1] ⊗ Δ[n] ⟶ Δ[n]` of `Δ[n]` onto its vertex `0`: on a simplex `(t, x)`
it is `l ↦ if t l = 1 then x l else 0`. It is the identity at time `1` and the constant map at
the vertex `0` at time `0`. -/
def prismContraction (n : ℕ) : Δ[1] ⊗ Δ[n] ⟶ Δ[n] where
  app m := ↾fun (x : (Δ[1] ⊗ Δ[n] : SSet.{u}).obj m) ↦ stdSimplex.objMk
    (prismContractionOrderHom (stdSimplex.objEquiv x.1).toOrderHom
      (stdSimplex.objEquiv x.2).toOrderHom)
  naturality _ _ _ := rfl

lemma prismContraction_app_apply {n d : ℕ} (x : (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌) (l : Fin (d + 1)) :
    (prismContraction n).app _ x l = if x.1 l = 1 then x.2 l else 0 := rfl

/-- The inclusion `Y ⟶ Δ[1] ⊗ Y` at time `0`. -/
noncomputable def ι₀Left (Y : SSet.{u}) : Y ⟶ Δ[1] ⊗ Y :=
  lift (const (stdSimplex.obj₀Equiv.symm 0)) (𝟙 Y)

/-- The inclusion `Y ⟶ Δ[1] ⊗ Y` at time `1`. -/
noncomputable def ι₁Left (Y : SSet.{u}) : Y ⟶ Δ[1] ⊗ Y :=
  lift (const (stdSimplex.obj₀Equiv.symm 1)) (𝟙 Y)

lemma ι₁Left_naturality {Y Y' : SSet.{u}} (f : Y ⟶ Y') : ι₁Left Y ≫ Δ[1] ◁ f = f ≫ ι₁Left Y' := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [ι₁Left]

lemma ι₀Left_naturality {Y Y' : SSet.{u}} (f : Y ⟶ Y') : ι₀Left Y ≫ Δ[1] ◁ f = f ≫ ι₀Left Y' := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [ι₀Left]

@[simp]
lemma ι₁Left_app_fst_apply {Y : SSet.{u}} {d : ℕ} (y : Y _⦋d⦌) (k : Fin (d + 1)) :
    dsimp% ((ι₁Left Y).app _ y).1 k = 1 := rfl

@[simp]
lemma ι₁Left_app_snd {Y : SSet.{u}} {m : SimplexCategoryᵒᵖ} (y : Y.obj m) :
    dsimp% ((ι₁Left Y).app _ y).2 = y := rfl

@[simp]
lemma ι₀Left_app_fst_apply {Y : SSet.{u}} {d : ℕ} (y : Y _⦋d⦌) (k : Fin (d + 1)) :
    dsimp% ((ι₀Left Y).app _ y).1 k = 0 := rfl

@[simp]
lemma ι₀Left_app_snd {Y : SSet.{u}} {m : SimplexCategoryᵒᵖ} (y : Y.obj m) :
    dsimp% ((ι₀Left Y).app _ y).2 = y := rfl

lemma ι₁Left_prismContraction (n : ℕ) : ι₁Left Δ[n] ≫ prismContraction.{u} n = 𝟙 _ := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  apply stdSimplex.ext
  intro l
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, prismContraction_app_apply]
  simp

lemma ι₀Left_prismContraction (n : ℕ) :
    ι₀Left Δ[n] ≫ prismContraction.{u} n = const (stdSimplex.obj₀Equiv.symm 0) := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  apply stdSimplex.ext
  intro l
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, prismContraction_app_apply]
  simp
  rfl

/-! ### Maps between standard simplices -/

/-- Evaluating a map `Δ[k] ⟶ Δ[n]` on a simplex `objEquiv.symm f` of `Δ[k]`. -/
lemma app_objEquiv_symm_apply {k n m : ℕ} (φ : Δ[k] ⟶ Δ[n]) (f : ⦋m⦌ ⟶ ⦋k⦌) (l : Fin (m + 1)) :
    (φ.app _ (stdSimplex.objEquiv.symm f) : Δ[n] _⦋m⦌) l = (yonedaEquiv φ) (f.toOrderHom l) := by
  rw [← yonedaEquiv.symm_apply_apply φ, yonedaEquiv_symm_app_objEquiv_symm]
  rfl

lemma app_objMk_apply {k n m : ℕ} (φ : Δ[k] ⟶ Δ[n]) (f : Fin (m + 1) →o Fin (k + 1))
    (l : Fin (m + 1)) :
    (φ.app _ (stdSimplex.objMk f) : Δ[n] _⦋m⦌) l = (yonedaEquiv φ) (f l) :=
  app_objEquiv_symm_apply φ _ l

/-- A map between standard simplices is determined by its values on a subcomplex containing
all vertices. -/
lemma hom_ext_of_obj_zero_eq_top {k n : ℕ} (S : (Δ[k] : SSet.{u}).Subcomplex)
    (hS : S.obj (op ⦋0⦌) = ⊤) (φ ψ : Δ[k] ⟶ Δ[n]) (h : S.ι ≫ φ = S.ι ≫ ψ) : φ = ψ := by
  apply yonedaEquiv.injective
  apply stdSimplex.ext
  intro l
  have hl : stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋k⦌ l) ∈ S.obj (op ⦋0⦌) := by
    rw [hS]; trivial
  have this :
      (φ.app (op ⦋0⦌) (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋k⦌ l)) : Δ[n] _⦋0⦌) 0 =
      (ψ.app (op ⦋0⦌) (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋k⦌ l)) : Δ[n] _⦋0⦌) 0 :=
    congr_arg (fun f : S.toSSet ⟶ Δ[n] ↦ (f.app (op ⦋0⦌) ⟨_, hl⟩ : Δ[n] _⦋0⦌) 0) h
  rw [app_objEquiv_symm_apply, app_objEquiv_symm_apply] at this
  exact this

/-! ### Vertex inclusions of `Δ[1]` -/

lemma face_zero_ι_eq_const :
    (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι =
      const (stdSimplex.obj₀Equiv.symm 0) := by
  rw [← Category.id_comp (stdSimplex.face {0}).ι,
    ← (stdSimplex.faceSingletonIso (0 : Fin 2)).inv_hom_id, Category.assoc,
    stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ, stdSimplex.δ_one_eq_const, comp_const]

lemma horn_one_zero_ι_eq_const :
    (Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).ι = const (stdSimplex.obj₀Equiv.symm 0) := by
  have : ∀ (S : (Δ[1] : SSet.{u}).Subcomplex), S = stdSimplex.face {0} →
      S.ι = const (stdSimplex.obj₀Equiv.symm 0) := by
    rintro _ rfl
    exact face_zero_ι_eq_const
  exact this _ horn_one_zero_eq_face

/-- The vertex inclusion `{1} ⟶ Δ[1]`, written as a constant map, is right anodyne. -/
lemma rightAnodyneExtensions_const_one :
    rightAnodyneExtensions (const (stdSimplex.obj₀Equiv.symm 1) : Δ[0] ⟶ Δ[1]) := by
  rw [← stdSimplex.δ_zero_eq_const, ← stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]
  exact MorphismProperty.comp_mem _ _ _ (rightAnodyneExtensions.of_isIso _)
    rightAnodyneExtensions_face_one_ι

lemma whiskerRight_const {X Z : SSet.{u}} (z : Z _⦋0⦌) (Y : SSet.{u}) :
    (const z : X ⟶ Z) ▷ Y = snd X Y ≫ lift (const z) (𝟙 Y) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

instance isIso_lift_const_id (Y : SSet.{u}) :
    IsIso (lift (const (stdSimplex.obj₀Equiv.symm 0) : Y ⟶ Δ[0]) (𝟙 Y)) :=
  ⟨⟨snd Δ[0] Y, lift_snd _ _, by
    apply CartesianMonoidalCategory.hom_ext
    · exact stdSimplex.ext₀
    · simp⟩⟩

/-- The inclusion `ι₁Left Y : Y ⟶ Δ[1] ⊗ Y` at time `1` is right anodyne: it is the composite
`Y ≅ Δ[0] ⊗ Y ⟶ Δ[1] ⊗ Y` of an isomorphism and the whiskered vertex inclusion `{1} ⟶ Δ[1]`. -/
lemma rightAnodyneExtensions_ι₁Left (Y : SSet.{u}) : rightAnodyneExtensions (ι₁Left Y) := by
  have h : ι₁Left Y = lift (const (stdSimplex.obj₀Equiv.symm 0) : Y ⟶ Δ[0]) (𝟙 Y) ≫
      (const (stdSimplex.obj₀Equiv.symm 1) : Δ[0] ⟶ Δ[1]) ▷ Y := by
    rw [whiskerRight_const, lift_snd_assoc, Category.id_comp]
    rfl
  rw [h]
  refine MorphismProperty.comp_mem _ _ _ (rightAnodyneExtensions.of_isIso _)
    (rightAnodyneExtensions_const_one.whiskerRight Y)

/-! ### Outer horn filling for a right fibration over `Δ[n]`

If `τ : Δ[d + 1] ⟶ Δ[n]` sends both vertices `0` and `1` to the vertex `0`, then any map
`Λ[d + 1, 0] ⟶ E` over `τ` extends to `Δ[d + 1]` over `τ`: for `d = 0` the horn is a point;
for `d ≥ 1` the edge `0 → 1` of the horn lies in the fiber over `0`, which is a Kan complex, so
this edge is an equivalence and the outer horn can be filled (Kerodon 019F). -/

lemma exists_fill_face_zero_of_rightFibration {n : ℕ} {E : SSet.{u}} (q : E ⟶ Δ[n])
    (τ : Δ[1] ⟶ Δ[n]) (hτ : ∀ l : Fin 2, l ≤ 1 → (yonedaEquiv τ) l = 0)
    (σ₀ : (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).toSSet ⟶ E)
    (hσ : σ₀ ≫ q = (stdSimplex.face {0}).ι ≫ τ) :
    ∃ w : Δ[1] ⟶ E, (stdSimplex.face {0}).ι ≫ w = σ₀ ∧ w ≫ q = τ := by
  have hτ' : τ = const (stdSimplex.obj₀Equiv.symm 0) := by
    apply yonedaEquiv.injective
    apply stdSimplex.ext
    intro l
    rw [hτ l (Fin.le_last l)]
    rfl
  set e := stdSimplex.faceSingletonIso (0 : Fin 2)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E _⦋0⦌, e.hom ≫ σ₀ = yonedaEquiv.symm x₀ :=
    ⟨_, (yonedaEquiv.symm_apply_apply _).symm⟩
  have hσ₀ : σ₀ = const x₀ := by
    rw [← e.inv_hom_id_assoc σ₀, hx₀, yonedaEquiv_symm_zero, comp_const]
  have h1 : q.app _ x₀ = stdSimplex.obj₀Equiv.symm 0 := by
    have := congr_arg (fun f : (stdSimplex.face {0}).toSSet ⟶ Δ[n] ↦ yonedaEquiv (e.hom ≫ f)) hσ
    simp only [hσ₀, hτ', const_comp, comp_const, yonedaEquiv_const] at this
    exact this
  refine ⟨const x₀, ?_, ?_⟩
  · rw [hσ₀, comp_const]
  · rw [const_comp, h1, hτ']

lemma exists_fill_outerHorn_of_rightFibration {n : ℕ} {E : SSet.{u}} (q : E ⟶ Δ[n])
    [RightFibration q] (d : ℕ) (i : Fin (d + 2)) (hi : i = 0) (τ : Δ[d + 1] ⟶ Δ[n])
    (hτ : ∀ l : Fin (d + 2), l ≤ 1 → (yonedaEquiv τ) l = 0)
    (σ₀ : (Λ[d + 1, i] : SSet.{u}) ⟶ E) (hσ : σ₀ ≫ q = Λ[d + 1, i].ι ≫ τ) :
    ∃ w : Δ[d + 1] ⟶ E, Λ[d + 1, i].ι ≫ w = σ₀ ∧ w ≫ q = τ := by
  subst hi
  cases d with
  | zero =>
    have key : ∀ (S : (Δ[1] : SSet.{u}).Subcomplex), S = stdSimplex.face {0} →
        ∀ (σ₀ : S.toSSet ⟶ E), σ₀ ≫ q = S.ι ≫ τ →
          ∃ w : Δ[1] ⟶ E, S.ι ≫ w = σ₀ ∧ w ≫ q = τ := by
      rintro _ rfl σ₀ hσ
      exact exists_fill_face_zero_of_rightFibration q τ hτ σ₀ hσ
    exact key _ horn_one_zero_eq_face σ₀ hσ
  | succ m =>
    have : Quasicategory E := quasicategory_of_innerFibration q
    obtain ⟨s, hs⟩ : ∃ s : E _⦋1⦌, σ₀.app _ (horn.edge₀₁ m) = s := ⟨_, rfl⟩
    have hqs : q.app _ s = yonedaEquiv (const (stdSimplex.obj₀Equiv.symm 0) : Δ[1] ⟶ Δ[n]) := by
      apply stdSimplex.ext
      intro l
      have : q.app _ s = τ.app _ (stdSimplex.edge (m + 2) 0 1 (Fin.zero_le _)) := by
        rw [← hs]
        change (σ₀ ≫ q).app _ (horn.edge₀₁ m) = _
        rw [hσ]
        rfl
      rw [this, stdSimplex.edge, app_objMk_apply, hτ _ (by fin_cases l <;> simp)]
      rfl
    have hs' : yonedaEquiv.symm s ≫ q =
        toUnit _ ≫ const (stdSimplex.obj₀Equiv.symm 0) := by
      rw [comp_const, yonedaEquiv_symm_comp, hqs, Equiv.symm_apply_apply]
    let eF : Δ[1] ⟶ fiber q (stdSimplex.obj₀Equiv.symm 0) := pullback.lift _ _ hs'
    have heF : eF ≫ fiberι q _ = yonedaEquiv.symm s := pullback.lift_fst _ _ _
    have he : (Edge.mk' s).IsEquiv := by
      refine Edge.IsEquiv.ofEq
        ((KanComplex.isEquiv_edge (Edge.mk' (yonedaEquiv eF))).map (fiberι q _)) ?_
      rw [Edge.map_edge, Edge.mk'_edge, Edge.mk'_edge, ← yonedaEquiv_comp, heF,
        Equiv.apply_symm_apply]
    rw [← hs] at he
    obtain ⟨σ, hσ'⟩ := fillOuterHornOfIsEquiv σ₀ he
    refine ⟨σ, hσ'.symm, ?_⟩
    refine hom_ext_of_obj_zero_eq_top Λ[m + 2, 0] (horn_obj_zero m 0) _ _ ?_
    rw [← Category.assoc, ← hσ', hσ]

/-! ### The section over `Δ[n]` -/

/-- For an index-`0` cell `c` of a pairing of a subcomplex `A ⊆ Δ[1] ⊗ Δ[n]` containing
`Δ[1] ⊗ ∂Δ[n]`, the second component of the simplex `c.map` of `Δ[1] ⊗ Δ[n]` sends the
vertices `0` and `1` to `0`: its `0`-th face is not in `A`, hence its second component is
surjective onto `Fin (n + 1)`, so some `i ≥ 1` is sent to `0`. -/
lemma snd_apply_eq_zero_of_index_eq_zero {n : ℕ}
    {A : (Δ[1] ⊗ Δ[n] : SSet.{u}).Subcomplex}
    (hA : ∀ {d : ℕ} (x : (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌), x ∉ A.obj _ → x.2 ∉ ∂Δ[n].obj _)
    {P : A.Pairing} [P.IsProper] {f : P.RankFunction ℕ} {j : ℕ} (c : f.Cell j)
    (hc : c.index = 0) (y : (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋c.dim + 1⦌)
    (hy : c.map = yonedaEquiv.symm y) (l : Fin (c.dim + 2)) (hl : l ≤ 1) : y.2 l = 0 := by
  have key : (Δ[1] ⊗ Δ[n]).map (SimplexCategory.δ (0 : Fin (c.dim + 2))).op y =
      c.s.val.simplex := by
    rw [← hc, ← yonedaEquiv_symm_app_objEquiv_symm, ← hy]
    exact c.map_app_objEquiv_symm_δ_index
  have h₂ := hA _ (key ▸ c.s.val.notMem)
  rw [mem_boundary_iff_notMem_range] at h₂
  simp only [not_exists, not_not] at h₂
  obtain ⟨i, hi⟩ := h₂ 0
  have hi' : y.2 i.succ = 0 := by
    rw [← hi]
    change _ = y.2 ((0 : Fin (c.dim + 2)).succAbove i)
    rw [Fin.zero_succAbove]
  refine le_antisymm ?_ (Fin.zero_le _)
  rw [← hi']
  refine stdSimplex.monotone_apply y.2 (hl.trans ?_)
  rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_one]
  omega

/-- **Boundary extension over a simplex.** A right fibration `q : E ⟶ Δ[n]` with weakly
contractible fibers admits a section over `Δ[n]` extending any given section over `∂Δ[n]`. -/
theorem exists_section_of_rightFibration_stdSimplex {n : ℕ} {E : SSet.{u}} (q : E ⟶ Δ[n])
    [RightFibration q] (h : ∀ j : Δ[n] _⦋0⦌, WeaklyContractible (fiber q j))
    (a : (∂Δ[n] : SSet.{u}) ⟶ E) (ha : a ≫ q = ∂Δ[n].ι) :
    ∃ l : Δ[n] ⟶ E, ∂Δ[n].ι ≫ l = a ∧ l ≫ q = 𝟙 _ := by
  -- Step (a): deform `a` along the prism contraction back to time `0`.
  have sq₁ : CommSq a (ι₁Left (∂Δ[n] : SSet.{u})) q (Δ[1] ◁ ∂Δ[n].ι ≫ prismContraction n) :=
    ⟨by rw [ha, ← Category.assoc, ι₁Left_naturality, Category.assoc, ι₁Left_prismContraction,
      Category.comp_id]⟩
  have : HasLiftingProperty (ι₁Left (∂Δ[n] : SSet.{u})) q :=
    rightAnodyneExtensions_ι₁Left _ _ (mem_rightFibrations q)
  obtain ⟨A', hA'₁, hA'₂⟩ : ∃ A' : Δ[1] ⊗ (∂Δ[n] : SSet.{u}) ⟶ E, ι₁Left _ ≫ A' = a ∧
      A' ≫ q = Δ[1] ◁ ∂Δ[n].ι ≫ prismContraction n :=
    ⟨sq₁.lift, sq₁.fac_left, sq₁.fac_right⟩
  -- Step (b): at time `0` the deformed map lands in the fiber over the vertex `0`.
  have ha₀' : (ι₀Left _ ≫ A') ≫ q = toUnit _ ≫ const (stdSimplex.obj₀Equiv.symm 0) := by
    rw [comp_const, Category.assoc, hA'₂, ← Category.assoc, ι₀Left_naturality, Category.assoc,
      ι₀Left_prismContraction, comp_const]
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : (∂Δ[n] : SSet.{u}) ⟶ fiber q (stdSimplex.obj₀Equiv.symm 0),
      f₀ ≫ fiberι q _ = ι₀Left _ ≫ A' :=
    ⟨pullback.lift _ _ ha₀', pullback.lift_fst _ _ _⟩
  -- Step (c): extend over `Δ[n]` inside the weakly contractible Kan complex `fiber q 0`.
  have sq₂ : CommSq f₀ ∂Δ[n].ι (terminal.from (fiber q (stdSimplex.obj₀Equiv.symm 0)))
      (terminal.from Δ[n]) := ⟨Subsingleton.elim _ _⟩
  have : HasLiftingProperty ∂Δ[n].ι
      (terminal.from (fiber q (stdSimplex.obj₀Equiv.symm 0))) :=
    rlp_monomorphisms_terminal_from_of_weaklyContractible (h _) _
      (MorphismProperty.monomorphisms.infer_property _)
  obtain ⟨a₀, ha₀₁, ha₀₂⟩ : ∃ a₀ : Δ[n] ⟶ E, ∂Δ[n].ι ≫ a₀ = ι₀Left _ ≫ A' ∧
      a₀ ≫ q = const (stdSimplex.obj₀Equiv.symm 0) :=
    ⟨sq₂.lift ≫ fiberι q _, by rw [← Category.assoc, sq₂.fac_left, hf₀],
      by rw [Category.assoc, fiberι_comp_eq_const, comp_const]⟩
  -- Step (d): glue the two pieces to `Λ[1, 0].unionProd ∂Δ[n]`.
  have hglue : (Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).ι ▷ (∂Δ[n] : SSet.{u}) ≫ A' =
      (Λ[1, 0] : SSet.{u}) ◁ ∂Δ[n].ι ≫ snd _ _ ≫ a₀ := by
    rw [horn_one_zero_ι_eq_const, whiskerRight_const, whiskerLeft_snd_assoc, ha₀₁,
      Category.assoc]
    rfl
  obtain ⟨top, htop₁, htop₂⟩ : ∃ top : (Λ[1, 0].unionProd ∂Δ[n] : SSet.{u}) ⟶ E,
      Subcomplex.unionProd.ι₁ _ _ ≫ top = A' ∧
      Subcomplex.unionProd.ι₂ _ _ ≫ top = snd _ _ ≫ a₀ :=
    ⟨(Subcomplex.unionProd.isPushout _ _).desc _ _ hglue,
      (Subcomplex.unionProd.isPushout _ _).inl_desc _ _ _,
      (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _⟩
  have htop : top ≫ q = (Λ[1, 0].unionProd ∂Δ[n]).ι ≫ prismContraction n := by
    apply (Subcomplex.unionProd.isPushout _ _).hom_ext
    · rw [← Category.assoc, htop₁, hA'₂, Subcomplex.unionProd.ι₁_ι_assoc]
    · rw [← Category.assoc, htop₂, Subcomplex.unionProd.ι₂_ι_assoc, Category.assoc, ha₀₂,
        comp_const, horn_one_zero_ι_eq_const, whiskerRight_const, Category.assoc]
      change _ = snd _ _ ≫ ι₀Left Δ[n] ≫ prismContraction n
      rw [ι₀Left_prismContraction, comp_const]
  -- Step (e): extend to `Δ[1] ⊗ Δ[n]` cell by cell; the index-`0` cells are outer horns
  -- whose first edge lies in the fiber over `0`.
  obtain ⟨L, hL₁, hL₂⟩ : ∃ L : Δ[1] ⊗ Δ[n] ⟶ E,
      (Λ[1, 0].unionProd ∂Δ[n]).ι ≫ L = top ∧ L ≫ q = prismContraction n :=
    Subcomplex.Pairing.RankFunction.exists_lift_of_rightFibration
    (prodStdSimplex.pairingCore.{u} (0 : Fin 1) n).pairing.rankFunction q (prismContraction n)
    top htop (by
      intro j c v hv _ hc
      obtain ⟨y, hy⟩ : ∃ y, c.map = yonedaEquiv.symm y := ⟨_, rfl⟩
      refine exists_fill_outerHorn_of_rightFibration q c.dim c.index hc
        (c.map ≫ prismContraction n) ?_ (c.mapHorn ≫ v) ?_
      · intro l hl
        rw [hy, yonedaEquiv_symm_comp, Equiv.apply_symm_apply, prismContraction_app_apply,
          snd_apply_eq_zero_of_index_eq_zero (fun x hx h₂ ↦
            hx ((Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inl h₂))) c hc y hy l hl, ite_self]
      · rw [Category.assoc, hv, ← Category.assoc,
          Subcomplex.Pairing.RankFunction.Cell.mapHorn_ι, Category.assoc])
  refine ⟨ι₁Left Δ[n] ≫ L, ?_, ?_⟩
  · rw [← Category.assoc, ← ι₁Left_naturality, Category.assoc,
      ← Subcomplex.unionProd.ι₁_ι Λ[1, 0] ∂Δ[n], Category.assoc, hL₁, htop₁, hA'₁]
  · rw [Category.assoc, hL₂, ι₁Left_prismContraction]

/-! ### The main theorem -/

/-- **Right fibrations with weakly contractible fibers are trivial fibrations**
([Lur09, 2.1.3.4] flavour; Kerodon 4.4.2). A right fibration `q : E ⟶ B` all of whose fibers
are weakly contractible has the right lifting property against all monomorphisms of simplicial
sets. -/
theorem rlp_monomorphisms_of_rightFibration_of_weaklyContractible_fibers
    {E B : SSet.{u}} (q : E ⟶ B) [RightFibration q]
    (h : ∀ b : B _⦋0⦌, WeaklyContractible (fiber q b)) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp q := by
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  constructor
  intro a g sq
  -- pull back `q` along `g : Δ[n] ⟶ B`: a right fibration over `Δ[n]` with the same fibers.
  have : RightFibration (pullback.snd q g) :=
    ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback q g) (mem_rightFibrations q)⟩
  have hfib : ∀ j : Δ[n] _⦋0⦌, WeaklyContractible (fiber (pullback.snd q g) j) := by
    intro j
    exact weaklyContractible_of_isWeakHomotopyEquivalence
      ((pullbackLeftPullbackSndIso q g (const j : 𝟙_ SSet.{u} ⟶ Δ[n])).hom ≫
        (pullback.congrHom rfl (const_comp j g)).hom)
      (IsHomotopyEquivalence.of_isIso _).isWeakHomotopyEquivalence (h _)
  obtain ⟨l, hl₁, hl₂⟩ := exists_section_of_rightFibration_stdSimplex (pullback.snd q g) hfib
    (pullback.lift a ∂Δ[n].ι sq.w) (pullback.lift_snd _ _ _)
  exact ⟨⟨⟨l ≫ pullback.fst q g, by rw [← Category.assoc, hl₁, pullback.lift_fst],
    by rw [Category.assoc, pullback.condition, ← Category.assoc, hl₂, Category.id_comp]⟩⟩⟩

end SSet
