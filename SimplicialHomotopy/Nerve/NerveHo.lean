/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Cofinal.Cofinal
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
# Maps from a quasicategory to a nerve, and the canonical functor `C ⟶ N(hC)`

* `SSet.innerFibrations_to_nerve`, `SSet.innerFibration_to_nerve` : a map
  from a quasicategory to the nerve of an arbitrary small category is an inner fibration.
  Proof: a simplex of a nerve is determined by its spine (`Nerve.isStrictSegal`), and every
  inner horn contains the spine of the simplex (`horn.spineId`).
* `SSet.toNerveHo C : C ⟶ nerve C.HomotopyCategory` : the canonical functor, defined directly
  on simplices (vertex `i ↦ HomotopyCategory.mk`, edge `i ≤ j ↦ homMk` of the edge `i → j`).
* `SSet.innerFibration_toNerveHo` : `toNerveHo C` is an inner fibration when `C` is a
  quasicategory.
* `SSet.fiberHo C y` : the fiber `Fun(Δ[n], C) ×_{Fun(Δ[n], N hC)} Δ[0]` over an
  `n`-simplex `y` of `N(hC)`; it is a quasicategory.
-/

universe u

open CategoryTheory Limits Opposite Simplicial

namespace SSet

/-! ### Spines and the Yoneda bijection -/

/-- `Path.map` is functorial in the map of simplicial sets. -/
lemma Path.map_comp {X Y Z : SSet.{u}} {n : ℕ} (p : Path X n) (f : X ⟶ Y) (g : Y ⟶ Z) :
    p.map (f ≫ g) = (p.map f).map g :=
  rfl

/-- The spine of the `m`-simplex `yonedaEquiv f` is the image under `f : Δ[m] ⟶ X` of the
spine of the generic simplex of `Δ[m]`. -/
lemma spine_yonedaEquiv {X : SSet.{u}} {m : ℕ} (f : Δ[m] ⟶ X) :
    X.spine m (yonedaEquiv f) = (stdSimplex.spineId m).map f := by
  apply Path.ext
  · funext i
    rw [spine_vertex, yonedaEquiv_naturality, yonedaEquiv_comp]
    rfl
  · funext i
    rw [spine_arrow, yonedaEquiv_naturality, yonedaEquiv_comp]
    rfl

/-! ### Maps from a quasicategory to a nerve are inner fibrations -/

section General

variable {X : SSet.{u}} [Quasicategory X] {A : Type u} [Category.{u} A]

/-- A map from a quasicategory to the nerve of any small category is an
inner fibration (`MorphismProperty` form). -/
theorem innerFibrations_to_nerve (F : X ⟶ nerve A) : innerFibrations F := by
  rintro _ _ _ ⟨i, h0, hn⟩
  constructor
  intro u v sq
  obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling h0 hn u
  refine ⟨⟨⟨σ, hσ.symm, ?_⟩⟩⟩
  have hw : Λ[_ + 2, i].ι ≫ σ ≫ F = Λ[_ + 2, i].ι ≫ v := by
    rw [← Category.assoc, ← hσ, sq.w]
  apply yonedaEquiv.injective
  apply (IsStrictSegal.segal (X := nerve A) _).injective
  rw [spine_yonedaEquiv, spine_yonedaEquiv, ← horn.spineId_map_hornInclusion i h0 hn,
    ← Path.map_comp, ← Path.map_comp, hw]

/-- `innerFibrations_to_nerve`, class form. -/
theorem innerFibration_to_nerve (F : X ⟶ nerve A) : InnerFibration F :=
  ⟨innerFibrations_to_nerve F⟩

end General

/-! ### The canonical functor `C ⟶ N(hC)` -/

section ToNerveHo

open HomotopyCategory

variable (C : SSet.{u})

/-- Faces of a simplex `C.map φ.op x`, as simplices of the form `C.map ψ.op x`. -/
lemma δ_map_op_apply {n m : ℕ} (x : C _⦋n⦌) (φ : ⦋m + 1⦌ ⟶ ⦋n⦌) (k : Fin (m + 2)) :
    C.δ k (C.map φ.op x) = C.map (SimplexCategory.δ k ≫ φ).op x := by
  rw [SimplicialObject.δ_def, ← Functor.map_comp_apply, op_comp]

lemma _root_.SimplexCategory.δ_one_comp_mkOfLe {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) :
    SimplexCategory.δ 1 ≫ SimplexCategory.mkOfLe i j h = SimplexCategory.const ⦋0⦌ ⦋n⦌ i :=
  SimplexCategory.Hom.ext_zero_left _ _

lemma _root_.SimplexCategory.δ_zero_comp_mkOfLe {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) :
    SimplexCategory.δ 0 ≫ SimplexCategory.mkOfLe i j h = SimplexCategory.const ⦋0⦌ ⦋n⦌ j :=
  SimplexCategory.Hom.ext_zero_left _ _

lemma _root_.SimplexCategory.σ_zero_comp_const {n : ℕ} (i : Fin (n + 1)) :
    SimplexCategory.σ 0 ≫ SimplexCategory.const ⦋0⦌ ⦋n⦌ i = SimplexCategory.mkOfLe i i le_rfl :=
  SimplexCategory.Hom.ext_one_left _ _

lemma _root_.SimplexCategory.δ_two_comp_mkOfLeComp {n : ℕ} {i j k : Fin (n + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) :
    SimplexCategory.δ 2 ≫ SimplexCategory.mkOfLeComp i j k hij hjk =
      SimplexCategory.mkOfLe i j hij :=
  SimplexCategory.Hom.ext_one_left _ _

lemma _root_.SimplexCategory.δ_zero_comp_mkOfLeComp {n : ℕ} {i j k : Fin (n + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) :
    SimplexCategory.δ 0 ≫ SimplexCategory.mkOfLeComp i j k hij hjk =
      SimplexCategory.mkOfLe j k hjk :=
  SimplexCategory.Hom.ext_one_left _ _

lemma _root_.SimplexCategory.δ_one_comp_mkOfLeComp {n : ℕ} {i j k : Fin (n + 1)}
    (hij : i ≤ j) (hjk : j ≤ k) :
    SimplexCategory.δ 1 ≫ SimplexCategory.mkOfLeComp i j k hij hjk =
      SimplexCategory.mkOfLe i k (hij.trans hjk) :=
  SimplexCategory.Hom.ext_one_left _ _

lemma _root_.SimplexCategory.mkOfLe_comp {n m : ℕ} {i j : Fin (m + 1)} (h : i ≤ j) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    SimplexCategory.mkOfLe i j h ≫ φ =
      SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j) (φ.toOrderHom.monotone h) :=
  SimplexCategory.Hom.ext_one_left _ _

/-- The edge from the vertex `i` to the vertex `j` of an `n`-simplex `x` (for `i ≤ j`). -/
def edgeOfLe {n : ℕ} (x : C _⦋n⦌) {i j : Fin (n + 1)} (h : i ≤ j) :
    Edge (C.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x)
      (C.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j).op x) :=
  Edge.mk (C.map (SimplexCategory.mkOfLe i j h).op x)
    (by rw [δ_map_op_apply, SimplexCategory.δ_one_comp_mkOfLe])
    (by rw [δ_map_op_apply, SimplexCategory.δ_zero_comp_mkOfLe])

@[simp]
lemma edgeOfLe_edge {n : ℕ} (x : C _⦋n⦌) {i j : Fin (n + 1)} (h : i ≤ j) :
    (edgeOfLe C x h).edge = C.map (SimplexCategory.mkOfLe i j h).op x :=
  rfl

/-- The edge from a vertex to itself is the degenerate edge. -/
lemma edgeOfLe_refl {n : ℕ} (x : C _⦋n⦌) (i : Fin (n + 1)) :
    edgeOfLe C x (le_refl i) = Edge.id _ := by
  apply Edge.ext
  rw [edgeOfLe_edge, Edge.id_edge, SimplicialObject.σ_def, ← Functor.map_comp_apply,
    ← op_comp, SimplexCategory.σ_zero_comp_const]

/-- The `2`-simplex `x(i ≤ j ≤ k)` witnesses that the edge `i → k` is the composite of the
edges `i → j` and `j → k`. -/
def compStructOfLe {n : ℕ} (x : C _⦋n⦌) {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    Edge.CompStruct (edgeOfLe C x hij) (edgeOfLe C x hjk) (edgeOfLe C x (hij.trans hjk)) :=
  Edge.CompStruct.mk (C.map (SimplexCategory.mkOfLeComp i j k hij hjk).op x)
    (by rw [δ_map_op_apply, edgeOfLe_edge, SimplexCategory.δ_two_comp_mkOfLeComp])
    (by rw [δ_map_op_apply, edgeOfLe_edge, SimplexCategory.δ_zero_comp_mkOfLeComp])
    (by rw [δ_map_op_apply, edgeOfLe_edge, SimplexCategory.δ_one_comp_mkOfLeComp])

/-- The `n`-simplex of `N(hC)` attached to an `n`-simplex `x` of `C`: the objects are the
classes of the vertices of `x`, the morphisms are the classes of the edges of `x`. -/
def toNerveHoObj {n : ℕ} (x : C _⦋n⦌) : ComposableArrows C.HomotopyCategory n where
  obj i := HomotopyCategory.mk (C.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x)
  map {i j} f := homMk (edgeOfLe C x (leOfHom f))
  map_id i := by
    change homMk (edgeOfLe C x (le_refl i)) = _
    rw [edgeOfLe_refl, homMk_id]
  map_comp f g := (homMk_comp_homMk (compStructOfLe C x (leOfHom f) (leOfHom g))).symm

@[simp]
lemma toNerveHoObj_obj {n : ℕ} (x : C _⦋n⦌) (i : Fin (n + 1)) :
    (toNerveHoObj C x).obj i = HomotopyCategory.mk (C.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) :=
  rfl

lemma toNerveHoObj_map {n : ℕ} (x : C _⦋n⦌) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (toNerveHoObj C x).map f = homMk (edgeOfLe C x (leOfHom f)) :=
  rfl

/-- `homMk` of two edges with equal underlying `1`-simplices (and equal endpoints). -/
lemma homMk_eq_of_eq {X : SSet.{u}} {x₀ x₁ y₀ y₁ : X _⦋0⦌} (e : Edge x₀ x₁) (e' : Edge y₀ y₁)
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) (he : e.edge = e'.edge) :
    homMk e = eqToHom (congrArg HomotopyCategory.mk h₀) ≫ homMk e' ≫
      eqToHom (congrArg HomotopyCategory.mk h₁).symm := by
  subst h₀ h₁
  obtain rfl := Edge.ext he
  simp

/-- `nerve.homEquiv` of a transported edge. -/
lemma nerve_homEquiv_ofEq {A : Type u} [Category.{u} A]
    {x₀ x₁ y₀ y₁ : ComposableArrows A 0} (e : (nerve A).Edge x₀ x₁)
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) :
    nerve.homEquiv (e.ofEq h₀ h₁) =
      eqToHom (congrArg nerveEquiv h₀).symm ≫ nerve.homEquiv e ≫
        eqToHom (congrArg nerveEquiv h₁) := by
  subst h₀ h₁
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The vertex `i` of `C.map φ.op x` is the vertex `φ i` of `x`. -/
lemma vertex_map_op {n m : ℕ} (x : C _⦋n⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    C.map (SimplexCategory.const ⦋0⦌ ⦋m⦌ i).op (C.map φ.op x) =
      C.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom i)).op x := by
  rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp]

/-- Naturality of `toNerveHoObj` in the simplex. -/
lemma toNerveHoObj_map_op {n m : ℕ} (x : C _⦋n⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    toNerveHoObj C (C.map φ.op x) =
      (toNerveHoObj C x).whiskerLeft (SimplexCategory.toCat.map φ).toFunctor := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun i j f ↦ ?_)
  · exact congrArg HomotopyCategory.mk (vertex_map_op C x φ i)
  · exact homMk_eq_of_eq _ _ (vertex_map_op C x φ i) (vertex_map_op C x φ j)
      (by
        change C.map (SimplexCategory.mkOfLe i j (leOfHom f)).op (C.map φ.op x) =
          C.map (SimplexCategory.mkOfLe (φ.toOrderHom i) (φ.toOrderHom j)
            (φ.toOrderHom.monotone (leOfHom f))).op x
        rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.mkOfLe_comp])

/-- The canonical functor `C ⟶ N(hC)` from a simplicial set to the nerve of its homotopy
category, defined directly on simplices. -/
def toNerveHo : C ⟶ nerve C.HomotopyCategory where
  app Δ := ↾fun x ↦ toNerveHoObj C (n := Δ.unop.len) x
  naturality Δ Δ' f := by
    ext x
    exact toNerveHoObj_map_op C x f.unop

lemma toNerveHo_app {n : ℕ} (x : C _⦋n⦌) : (toNerveHo C).app _ x = toNerveHoObj C x :=
  rfl

/-- The `i`-th object of the image of an `n`-simplex `x` is the class of the `i`-th vertex
of `x`. -/
@[simp]
lemma toNerveHo_app_obj {n : ℕ} (x : C _⦋n⦌) (i : Fin (n + 1)) :
    ((toNerveHo C).app _ x).obj i =
      HomotopyCategory.mk (C.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) :=
  rfl

/-- The morphism `i ⟶ j` of the image of an `n`-simplex `x` is the class of the edge `i → j`
of `x`. -/
lemma toNerveHo_app_map' {n : ℕ} (x : C _⦋n⦌) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    ((toNerveHo C).app _ x).map' i j =
      homMk (edgeOfLe C x (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) (Fin.mk_le_mk.2 hij)) :=
  rfl

/-- Naturality of `toNerveHo` on simplices: the image of `C.map φ.op x` is the
reindexing of the image of `x` along `φ`. -/
lemma toNerveHo_app_map_op {n m : ℕ} (x : C _⦋n⦌) (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    (toNerveHo C).app _ (C.map φ.op x) =
      ((toNerveHo C).app _ x).whiskerLeft (SimplexCategory.toCat.map φ).toFunctor :=
  toNerveHoObj_map_op C x φ

/-- On vertices, `toNerveHo C` is `x ↦ HomotopyCategory.mk x`. -/
lemma toNerveHo_app_zero (x : C _⦋0⦌) :
    (toNerveHo C).app _ x = nerveEquiv.symm (HomotopyCategory.mk x) := by
  apply ComposableArrows.ext₀
  change HomotopyCategory.mk (C.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x) =
    HomotopyCategory.mk x
  rw [SimplexCategory.const_eq_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The source vertex of an edge, as `C.map (const ⦋0⦌ ⦋1⦌ 0).op`. -/
lemma map_const_zero_edge {x y : C _⦋0⦌} (e : Edge x y) :
    C.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op e.edge = x := by
  rw [← SimplexCategory.δ_one_eq_const, ← SimplicialObject.δ_def, e.src_eq]

/-- The target vertex of an edge, as `C.map (const ⦋0⦌ ⦋1⦌ 1).op`. -/
lemma map_const_one_edge {x y : C _⦋0⦌} (e : Edge x y) :
    C.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op e.edge = y := by
  rw [← SimplexCategory.δ_zero_eq_const, ← SimplicialObject.δ_def, e.tgt_eq]

/-- On edges, `toNerveHo C` is `e ↦ mk₁ (homMk e)`. -/
lemma toNerveHo_app_edge {x y : C _⦋0⦌} (e : Edge x y) :
    (toNerveHo C).app _ e.edge = ComposableArrows.mk₁ (homMk e) := by
  refine ComposableArrows.ext₁ (congrArg HomotopyCategory.mk (map_const_zero_edge C e))
    (congrArg HomotopyCategory.mk (map_const_one_edge C e)) ?_
  refine homMk_eq_of_eq _ _ (map_const_zero_edge C e) (map_const_one_edge C e) ?_
  change C.map (SimplexCategory.mkOfLe 0 1 (by decide)).op e.edge = e.edge
  rw [show SimplexCategory.mkOfLe (0 : Fin 2) 1 (by decide) = 𝟙 _ from
    SimplexCategory.Hom.ext_one_left _ _, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The edge `e.map (toNerveHo C)` of `N(hC)` (with endpoints rewritten via
`toNerveHo_app_zero`) is the edge attached to the morphism `homMk e`. -/
lemma toNerveHo_edge {x y : C _⦋0⦌} (e : Edge x y) :
    (e.map (toNerveHo C)).ofEq (toNerveHo_app_zero C x) (toNerveHo_app_zero C y) =
      nerve.edgeMk (homMk e) := by
  apply Edge.ext
  exact toNerveHo_app_edge C e

/-- Under `nerve.homEquiv`, the edge `e.map (toNerveHo C)` corresponds to `homMk e`. -/
lemma homEquiv_toNerveHo_edge {x y : C _⦋0⦌} (e : Edge x y) :
    nerve.homEquiv ((e.map (toNerveHo C)).ofEq (toNerveHo_app_zero C x)
      (toNerveHo_app_zero C y)) = homMk e := by
  rw [toNerveHo_edge]
  exact nerve.homEquiv_edgeMk _

/-- The canonical functor `C ⟶ N(hC)` is an inner fibration when
`C` is a quasicategory. -/
instance innerFibration_toNerveHo [Quasicategory C] : InnerFibration (toNerveHo C) :=
  innerFibration_to_nerve _

end ToNerveHo

/-! ### Fibers of `Fun(Δ[n], C) ⟶ Fun(Δ[n], N(hC))` -/

section FiberHo

open MonoidalCategory MonoidalClosed

/-- If `Fun(K, F) : Fun(K, X) ⟶ Fun(K, Y)` is an inner fibration, then its fiber
`relMap f F` over the point `f : K ⟶ Y` is a quasicategory: inner fibrations are stable under
base change, and a simplicial set is a quasicategory iff its map to the terminal object is an
inner fibration. -/
lemma quasicategory_relMap_of_innerFibration {K X Y : SSet.{u}} (F : X ⟶ Y)
    [InnerFibration ((ihom K).map F)] (f : K ⟶ Y) : Quasicategory (relMap f F) := by
  have : InnerFibration (pullback.snd ((ihom K).map F) (pointOf f)) :=
    ⟨innerFibrations.pullback_snd _ _
      (inferInstance : InnerFibration ((ihom K).map F)).mem⟩
  exact (quasicategory_iff_of_isTerminal _
    CartesianMonoidalCategory.isTerminalTensorUnit).2 this

variable (C : SSet.{u})

/-- For `F = toNerveHo C`: the fiber `Fun(Δ[n], C) ×_{Fun(Δ[n], N hC)} Δ[0]` of
`F_* : Fun(Δ[n], C) ⟶ Fun(Δ[n], N hC)` over the `n`-simplex `y` of `N(hC)`
(as the relative mapping space `Map_{N hC}(Δ[n], C)`). -/
noncomputable def fiberHo {n : ℕ} (y : (nerve C.HomotopyCategory) _⦋n⦌) : SSet.{u} :=
  relMap (yonedaEquiv.symm y) (toNerveHo C)

/-- The fibers `fiberHo C y` of `toNerveHo C` are quasicategories: `Fun(Δ[n], −)` preserves inner
fibrations, and the fiber of an inner fibration over a vertex is a quasicategory. -/
instance quasicategory_fiberHo [Quasicategory C] {n : ℕ}
    (y : (nerve C.HomotopyCategory) _⦋n⦌) : Quasicategory (fiberHo C y) :=
  quasicategory_relMap_of_innerFibration (toNerveHo C) (yonedaEquiv.symm y)

end FiberHo

end SSet
