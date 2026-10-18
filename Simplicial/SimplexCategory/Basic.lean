import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Fin

/-!
# The Simplex Category

We define the simplex category `SimplexCategory`, whose objects are natural numbers
`[n]` representing the finite totally ordered set `{0, 1, ..., n} = Fin (n+1)`,
and whose morphisms are order-preserving maps (monotone functions).

This is a pedagogical reconstruction — we import only Mathlib's `CategoryTheory`
and rebuild the simplex category from scratch.
-/

open CategoryTheory

universe u

/-- The simplex category `Δ`. Objects are natural numbers `n`, representing the
finite totally ordered set `[n] = {0, 1, ..., n}`. Morphisms are order-preserving
maps `Fin (n+1) →o Fin (m+1)`. -/
def SimplexCategory := ℕ

namespace SimplexCategory

-- The definition is made irreducible below; define the API first.

/-- Construct a simplex category object from a natural number. -/
def mk (n : ℕ) : SimplexCategory := n

/-- The "length" of a simplex category object: `[n]` has `n+1` elements. -/
def len (n : SimplexCategory) : ℕ := n

@[ext]
theorem ext (a b : SimplexCategory) : a.len = b.len → a = b := id

attribute [irreducible] SimplexCategory

/-- Notation `[n]` for `SimplexCategory.mk n`. -/
scoped[Simplicial] notation "[" n "]" => SimplexCategory.mk n

open Simplicial

@[simp]
theorem len_mk (n : ℕ) : [n].len = n := rfl

@[simp]
theorem mk_len (n : SimplexCategory) : ([n.len] : SimplexCategory) = n := rfl

instance : Inhabited SimplexCategory := ⟨mk 0⟩

/-- A recursor for `SimplexCategory`. Use it as `induction Δ using SimplexCategory.rec`. -/
protected def rec {F : SimplexCategory → Sort*} (h : ∀ n : ℕ, F [n]) : ∀ X, F X := fun n =>
  h n.len

/-- Morphisms in the simplex category are order-preserving maps. -/
protected def Hom (a b : SimplexCategory) :=
  Fin (a.len + 1) →o Fin (b.len + 1)

namespace Hom

/-- Construct a morphism from an order-preserving map. -/
def mk {a b : SimplexCategory} (f : Fin (a.len + 1) →o Fin (b.len + 1)) :
    SimplexCategory.Hom a b := f

/-- Extract the underlying order-preserving map. -/
def toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    Fin (a.len + 1) →o Fin (b.len + 1) := f

theorem ext' {a b : SimplexCategory} (f g : SimplexCategory.Hom a b) :
    f.toOrderHom = g.toOrderHom → f = g := id

attribute [irreducible] SimplexCategory.Hom

@[simp]
theorem mk_toOrderHom {a b : SimplexCategory} (f : SimplexCategory.Hom a b) :
    mk f.toOrderHom = f := rfl

@[simp]
theorem toOrderHom_mk {a b : SimplexCategory}
    (f : Fin (a.len + 1) →o Fin (b.len + 1)) : (mk f).toOrderHom = f := rfl

/-- Identity morphism. -/
@[simp]
def id (a : SimplexCategory) : SimplexCategory.Hom a a :=
  mk OrderHom.id

/-- Composition of morphisms. Note: `f : b ⟶ c`, `g : a ⟶ b`. -/
@[simp]
def comp {a b c : SimplexCategory} (f : SimplexCategory.Hom b c)
    (g : SimplexCategory.Hom a b) : SimplexCategory.Hom a c :=
  mk <| f.toOrderHom.comp g.toOrderHom

end Hom

/-- The simplex category, with objects `ℕ` and morphisms `OrderHom`. -/
instance smallCategory : SmallCategory.{0} SimplexCategory where
  Hom n m := SimplexCategory.Hom n m
  id m := SimplexCategory.Hom.id _
  comp f g := SimplexCategory.Hom.comp g f

@[simp]
theorem id_toOrderHom (a : SimplexCategory) :
    Hom.toOrderHom (𝟙 a) = OrderHom.id := rfl

@[simp]
theorem comp_toOrderHom {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).toOrderHom = g.toOrderHom.comp f.toOrderHom := rfl

-- `Hom.ext'` is not triggered automatically, so we add this after the Category instance.
@[ext]
theorem Hom.ext {a b : SimplexCategory} (f g : a ⟶ b) :
    f.toOrderHom = g.toOrderHom → f = g :=
  Hom.ext' _ _

end SimplexCategory
