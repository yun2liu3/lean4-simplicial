/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Comma.Over.Basic
import SimplicialHomotopy.Slice.Undercategory

/-!
# The undercategory of a nerve is the nerve of the undercategory

For a category `D` and an object `c : D`, the simplicial undercategory
`(nerve D)_{c/}` of `Slice/Undercategory.lean` ([Lur09, 1.2.9], defined by décalage)
is isomorphic over `nerve D` to the nerve of the categorical undercategory `Under c`:

* `SSet.underNerveIso c : ((nerve D).under (mk₀ c) : SSet) ≅ nerve (Under c)`;
* `SSet.underNerveIso_inv_comp_underProj` / `SSet.underNerveIso_hom_comp_nerveMap` : the
  isomorphism commutes with the projections to `nerve D`
  (`underProj` on the left, `nerveMap (Under.forget c)` on the right);
* `SSet.underNerveIso_hom_app_underId` : the identity vertex `underId` goes to `Under.mk (𝟙 c)`.

## Construction

An `m`-simplex of `(nerve D)_{c/}` is a chain `x = (x₀ → x₁ → ⋯ → x_{m+1})` in `D` whose cone
point `x₀` is `c` (`SSet.obj_zero_of_mem_under`, extracted from `SSet.decVertex_nerve`).

* `SSet.underOfNerve` (the inverse direction, `nerve (Under c) ⟶ (nerve D)_{c/}`): a chain
  `y = (y₀ → ⋯ → y_m)` in `Under c` goes to `(y ⋙ Under.forget c).precomp (y₀).hom`, the chain
  `c → y₀ → ⋯ → y_m` in `D`.
* `SSet.nerveOfUnder` (the forward direction): `x` goes to the chain `x₁ → ⋯ → x_{m+1}` made
  into a chain in `Under c` by the structure maps `c = x₀ → x_{i+1}`, using
  `CategoryTheory.Functor.toUnder` on `x.δ₀`.

## Organisation of the proofs

Naturality is proved once, for `underOfNerve`, by `ComposableArrows.ext_succ`: the tail
`δ₀` of both sides is *definitionally* `(y ⋙ Under.forget c).whiskerLeft φ`, because
`SimplexCategory.coneShiftHom` acts as `Fin.succ ∘ φ` on the non-cone vertices, so only the
first arrow needs an argument (`Under.w`). The two round trips are `ext_succ` (again with a
definitional `δ₀`, thanks to `Functor.toUnder_comp_forget`) and `ComposableArrows.ext`.
Naturality of the forward direction is deduced from injectivity of `underOfNerve`. The
`eqToHom`s produced by these extensionality lemmas are all along equalities whose two sides are
definitionally equal; they are discharged by the helpers `eqToHom_conj_of_eq`,
`eq_comp_eqToHom_of_eq` and `underMk_eqToHom_comp`, whose unification runs at default
transparency (`simp [eqToHom_refl]` would need the two sides to agree syntactically).

Universes: `D : Type u` with `Category.{v} D`, so that `nerve D`, `nerve (Under c)` and
`(nerve D)_{c/}` all live in `SSet.{max u v}`. `Under c : Type (max u v)`, and Mathlib's
`nerveMap` requires source and target categories in the same `Type` universe, so the
statement involving `nerveMap (Under.forget c)` is given for `D : Type u` with
`Category.{u} D` (a small category); the
universe-polymorphic content is `underProj_app_underOfNerve`.
-/

universe v u

open CategoryTheory Opposite Simplicial

namespace CategoryTheory

variable {D : Type u} [Category.{v} D]

/-! ### `eqToHom` helpers -/

lemma eqToHom_conj_of_eq {X Y : D} {f g : X ⟶ Y} (p : X = X) (q : Y = Y) (h : f = g) :
    f = eqToHom p ≫ g ≫ eqToHom q := by
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id, h]

lemma eq_comp_eqToHom_of_eq {X Y : D} {f g : X ⟶ Y} (q : Y = Y) (h : f = g) :
    f = g ≫ eqToHom q := by
  rw [eqToHom_refl, Category.comp_id, h]

lemma underMk_eqToHom_comp {c Y : D} (p : c = c) (f : c ⟶ Y) :
    Under.mk (eqToHom p ≫ f) = Under.mk f := by
  rw [eqToHom_refl, Category.id_comp]

end CategoryTheory

namespace SSet

section general

variable {D : Type u} [Category.{v} D]

/-! ### `precomp` on the arrows out of the new vertex -/

lemma precomp_map_zero_succ {n : ℕ} (F : ComposableArrows D n) {X : D} (f : X ⟶ F.left)
    (j : Fin (n + 1)) :
    (F.precomp f).map (homOfLE (Fin.zero_le j.succ)) = f ≫ F.map (homOfLE (Fin.zero_le j)) := by
  obtain ⟨_ | j, hj⟩ := j
  · show f = f ≫ F.map (𝟙 _)
    rw [F.map_id, Category.comp_id]
  · rfl

/-! ### The cone point of a simplex of `(nerve D).dec` -/

/-- The cone point of a simplex of `(nerve D).dec` is its `0`-th object. -/
lemma decVertex_nerve {m : SimplexCategoryᵒᵖ} (x : (nerve D).dec.obj m) :
    (nerve D).decVertex x = ComposableArrows.mk₀ (x.obj 0) :=
  ComposableArrows.ext₀ rfl

lemma obj_zero_of_mem_under (c : D) {m : SimplexCategoryᵒᵖ} {x : (nerve D).dec.obj m}
    (hx : x ∈ ((nerve D).under (ComposableArrows.mk₀ c)).obj m) : x.obj 0 = c :=
  congrArg (fun z : ComposableArrows D 0 ↦ z.obj 0)
    ((decVertex_nerve x).symm.trans ((mem_under_iff _ _ _).1 hx))

/-! ### The two directions -/

/-- `nerve (Under c) ⟶ (nerve D)_{c/}` on simplices: a chain `y₀ → ⋯ → y_m` in `Under c`
goes to the chain `c → y₀ → ⋯ → y_m` in `D`. -/
def underOfNerve (c : D) {m : SimplexCategoryᵒᵖ} (y : (nerve (Under c)).obj m) :
    ((nerve D).under (ComposableArrows.mk₀ c) : SSet.{max u v}).obj m :=
  ⟨ComposableArrows.precomp (y ⋙ Under.forget c) (y.obj 0).hom,
    (mem_under_iff _ _ _).2 (decVertex_nerve _)⟩

/-- `(nerve D)_{c/} ⟶ nerve (Under c)` on simplices: a chain `c = x₀ → x₁ → ⋯ → x_{m+1}` in `D`
goes to the chain `x₁ → ⋯ → x_{m+1}`, each `x_{i+1}` being an object of `Under c` through
`x₀ → x_{i+1}`. -/
def nerveOfUnder (c : D) {m : SimplexCategoryᵒᵖ}
    (x : ((nerve D).under (ComposableArrows.mk₀ c) : SSet.{max u v}).obj m) :
    (nerve (Under c)).obj m :=
  x.1.δ₀.toUnder c
    (fun i ↦ eqToHom (obj_zero_of_mem_under c x.2).symm ≫ x.1.map (homOfLE (Fin.zero_le i.succ)))
    (fun _ ↦ (Category.assoc _ _ _).trans (congrArg (eqToHom _ ≫ ·) (x.1.map_comp _ _).symm))

lemma underOfNerve_nerveOfUnder (c : D) {m : SimplexCategoryᵒᵖ}
    (x : ((nerve D).under (ComposableArrows.mk₀ c) : SSet.{max u v}).obj m) :
    underOfNerve c (nerveOfUnder c x) = x :=
  Subtype.ext (ComposableArrows.ext_succ (obj_zero_of_mem_under c x.2).symm rfl
    (congrArg (eqToHom _ ≫ ·) (eq_comp_eqToHom_of_eq _ rfl)))

lemma nerveOfUnder_underOfNerve (c : D) {m : SimplexCategoryᵒᵖ} (y : (nerve (Under c)).obj m) :
    nerveOfUnder c (underOfNerve c y) = y := by
  refine ComposableArrows.ext (fun i ↦ ?_) (fun i hi ↦ ?_)
  · obtain ⟨_ | i, hi⟩ := i
    · exact (underMk_eqToHom_comp (c := c) _ _).trans rfl
    · exact (underMk_eqToHom_comp (c := c) _ _).trans
        ((congrArg (Under.mk ·) (Under.w (y.map' 0 (i + 1)))).trans rfl)
  · refine Under.UnderMorphism.ext ?_
    rw [Under.comp_right, Under.comp_right, Under.eqToHom_right, Under.eqToHom_right]
    exact eqToHom_conj_of_eq _ _ rfl

lemma underOfNerve_injective (c : D) {m : SimplexCategoryᵒᵖ} :
    Function.Injective (underOfNerve c (m := m)) :=
  Function.LeftInverse.injective (nerveOfUnder_underOfNerve c)

/-- Naturality of `underOfNerve`: the tails agree definitionally, the first arrow by `Under.w`. -/
lemma underOfNerve_map (c : D) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    (y : (nerve (Under c)).obj m) :
    underOfNerve c ((nerve (Under c)).map f y) =
      ((nerve D).under (ComposableArrows.mk₀ c) : SSet.{max u v}).map f (underOfNerve c y) := by
  refine Subtype.ext (ComposableArrows.ext_succ rfl rfl ?_)
  exact eqToHom_conj_of_eq _ _ ((precomp_map_zero_succ (y ⋙ Under.forget c) (y.obj 0).hom
    ((SimplexCategory.toCat.map f.unop).toFunctor.obj (0 : Fin (n.unop.len + 1)))).trans
      (Under.w _)).symm

/-! ### The isomorphism -/

/-- The undercategory of a nerve is the nerve of the undercategory:
`(nerve D)_{c/} ≅ nerve (Under c)` ([Lur09, 1.2.9]). -/
def underNerveIso (c : D) :
    ((nerve D).under (ComposableArrows.mk₀ c) : SSet.{max u v}) ≅ nerve (Under c) where
  hom :=
    { app _ := ↾fun x ↦ nerveOfUnder c x
      naturality _ _ f := ConcreteCategory.hom_ext _ _ fun x ↦ underOfNerve_injective c (by
        change underOfNerve c (nerveOfUnder c
            (((nerve D).under (ComposableArrows.mk₀ c) : SSet.{max u v}).map f x)) =
          underOfNerve c ((nerve (Under c)).map f (nerveOfUnder c x))
        rw [underOfNerve_nerveOfUnder, underOfNerve_map, underOfNerve_nerveOfUnder]) }
  inv :=
    { app _ := ↾fun y ↦ underOfNerve c y
      naturality _ _ f := ConcreteCategory.hom_ext _ _ fun y ↦ underOfNerve_map c f y }
  hom_inv_id := NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun x ↦
    underOfNerve_nerveOfUnder c x)
  inv_hom_id := NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun y ↦
    nerveOfUnder_underOfNerve c y)

lemma underNerveIso_hom_app (c : D) {m : SimplexCategoryᵒᵖ}
    (x : ((nerve D).under (ComposableArrows.mk₀ c) : SSet.{max u v}).obj m) :
    (underNerveIso c).hom.app m x = nerveOfUnder c x := rfl

lemma underNerveIso_inv_app (c : D) {m : SimplexCategoryᵒᵖ} (y : (nerve (Under c)).obj m) :
    (underNerveIso c).inv.app m y = underOfNerve c y := rfl

/-! ### Compatibility with the projections to `nerve D` -/

/-- The projection `(nerve D)_{c/} ⟶ nerve D` composed with `underOfNerve` forgets the
structure maps: it is `y ↦ y ⋙ Under.forget c`, definitionally. -/
lemma underProj_app_underOfNerve (c : D) {m : SimplexCategoryᵒᵖ}
    (y : (nerve (Under c)).obj m) :
    ((nerve D).underProj (ComposableArrows.mk₀ c)).app m (underOfNerve c y) =
      y ⋙ Under.forget c := rfl

/-- The identity vertex `id_c` of `(nerve D)_{c/}` goes to `Under.mk (𝟙 c)`. -/
lemma underNerveIso_hom_app_underId (c : D) :
    (underNerveIso c).hom.app (op ⦋0⦌) ((nerve D).underId (ComposableArrows.mk₀ c)) =
      ComposableArrows.mk₀ (Under.mk (𝟙 c)) :=
  ComposableArrows.ext₀ (underMk_eqToHom_comp _ _)

end general

section small

/-! `nerveMap` needs its source and target in the same `Type` universe, while
`Under c : Type (max u v)` for `D : Type u`; so the statements against `nerveMap (Under.forget c)`
are given for `D : Type u` with `Category.{u} D`. -/

variable {D : Type u} [Category.{u} D]

/-- The inverse of `underNerveIso` followed by the projection `(nerve D)_{c/} ⟶ nerve D` is the
nerve of the forgetful functor `Under c ⥤ D`. -/
lemma underNerveIso_inv_comp_underProj (c : D) :
    (underNerveIso c).inv ≫ (nerve D).underProj (ComposableArrows.mk₀ c) =
      nerveMap (Under.forget c) :=
  NatTrans.ext (funext fun _ ↦ ConcreteCategory.hom_ext _ _ fun y ↦
    underProj_app_underOfNerve c y)

/-- `underNerveIso` is an isomorphism over `nerve D`. -/
lemma underNerveIso_hom_comp_nerveMap (c : D) :
    (underNerveIso c).hom ≫ nerveMap (Under.forget c) =
      (nerve D).underProj (ComposableArrows.mk₀ c) :=
  ((Iso.inv_comp_eq _).1 (underNerveIso_inv_comp_underProj c)).symm

end small

end SSet
