/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Functoriality of `nerveMap`

Mathlib defines `CategoryTheory.nerveMap : (C ⥤ D) → (nerve C ⟶ nerve D)` but proves no
functoriality lemma for it — only `nerveMap_app_mk₀` and `nerveMap_app_mk₁`. The two statements
below are both `rfl`.

They are stated in the namespace `CategoryTheory` rather than a namespace of this library, and in
a module of their own that imports nothing but Mathlib's `Nerve.lean`, because that is where they
would sit upstream.
-/

universe v u

namespace CategoryTheory

/-- The nerve of the identity functor is the identity. -/
lemma nerveMap_id {B : Type u} [Category.{v} B] : nerveMap (𝟭 B) = 𝟙 (nerve B) := rfl

/-- The nerve of a composite functor is the composite of the nerves. -/
lemma nerveMap_comp {B D E : Type u} [Category.{v} B] [Category.{v} D] [Category.{v} E]
    (G : B ⥤ D) (H : D ⥤ E) : nerveMap (G ⋙ H) = nerveMap G ≫ nerveMap H := rfl

end CategoryTheory
