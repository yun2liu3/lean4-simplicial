/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Horn.HornEdge
import SimplicialHomotopy.Anodyne.RightAnodyne
import SimplicialHomotopy.Equivalence.WeakEquivalenceKan

/-!
# Deformation retracts are right anodyne

If `s : C ⟶ E` is a monomorphism and `G : E ⊗ Δ[1] ⟶ E` is a homotopy from `𝟙 E` (time `0`)
to a map `q ≫ s` landing in `C` (time `1`) which maps `C ⊗ Δ[1]` into `C`, then `s` is a
right anodyne extension (in our convention right fibrations lift the right horns `Λ[n, i]`,
`0 < i`, and `{1} ↪ Δ[1]` is right anodyne). The special case where `G` is constant along `s`
is the classical "deformation retracts are anodyne" ([Lur09, proof of Proposition 4.1.2.15]).

**Proof.** Given a right fibration `r : X ⟶ Y` and a square `a : C ⟶ X`, `b : E ⟶ Y` with
`a ≫ r = s ≫ b`, the map `G ≫ b : E ⊗ Δ[1] ⟶ Y` already lifts on `E ⊗ {1} ∪ C ⊗ Δ[1]`
(by `q ≫ a` and `G' ≫ a`, where `G'` is the restriction of `G` to `C ⊗ Δ[1]`). The inclusion of
that union is
the pushout-product of the mono `s` with the right anodyne `{1} ↪ Δ[1]`, hence right anodyne,
so `G ≫ b` lifts to `L : E ⊗ Δ[1] ⟶ X`, and `ι₀ ≫ L` is the required lift of `b` through `r`
extending `a`.

This is the engine behind smoothness of left fibrations (`Smooth.lean`); the vertex case
`SSet.rightAnodyneExtensions_face_one_ι` is used in `TrivialFibration.lean`.
-/

universe u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory
open scoped Simplicial

namespace SSet

/-- The inclusion `X ⊗ {1} ⟶ X ⊗ Δ[1]` factors through `ι₁`. -/
lemma whiskerLeft_face_one_ι (X : SSet.{u}) :
    X ◁ (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι = fst _ _ ≫ ι₁ := by
  rw [← Category.id_comp (stdSimplex.face {1}).ι,
    ← (stdSimplex.faceSingletonIso (1 : Fin 2)).inv_hom_id, Category.assoc,
    stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ, stdSimplex.δ_zero_eq_const,
    MonoidalCategory.whiskerLeft_comp, whiskerLeft_const_one, ← Category.assoc,
    whiskerLeft_fst]

/-- The vertex inclusion `{1} ↪ Δ[1]` is right anodyne. -/
lemma rightAnodyneExtensions_face_one_ι :
    rightAnodyneExtensions (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  rw [← horn_one_one_eq_face]
  exact rightAnodyneExtensions.horn_ι (by decide)

/-- **Deformations into a subobject are right anodyne.** Let `s : C ⟶ E` be a monomorphism
and `G : E ⊗ Δ[1] ⟶ E` a homotopy starting at `𝟙 E` (time `0`), ending in `C` (time `1`,
`ι₁ ≫ G = q ≫ s`) and preserving `C` (`s ▷ Δ[1] ≫ G = G' ≫ s`). Then `s` is a right anodyne
extension. -/
theorem rightAnodyneExtensions_of_deformation {C E : SSet.{u}} (s : C ⟶ E) [Mono s] (q : E ⟶ C)
    (G : E ⊗ Δ[1] ⟶ E) (G' : C ⊗ Δ[1] ⟶ C) (hG₀ : ι₀ ≫ G = 𝟙 E) (hG₁ : ι₁ ≫ G = q ≫ s)
    (hGs : s ▷ Δ[1] ≫ G = G' ≫ s) : rightAnodyneExtensions s := by
  -- `G'` starts at the identity and ends at `s ≫ q`, since `G` does and `s` is mono
  have hG'₀ : ι₀ ≫ G' = 𝟙 C := by
    rw [← cancel_mono s, Category.assoc, ← hGs, ι₀_comp_assoc, hG₀, Category.comp_id,
      Category.id_comp]
  have hG'₁ : s ≫ q = ι₁ ≫ G' := by
    rw [← cancel_mono s, Category.assoc, Category.assoc, ← hGs, ι₁_comp_assoc, hG₁]
  intro X Y r hr
  constructor
  intro a b sq
  -- the pushout-product of `s` with `{1} ↪ Δ[1]`
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) s
    (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι
  have hι : rightAnodyneExtensions sq₁₂.ι :=
    rightAnodyneExtensions_pushoutObjObjι sq₁₂ rightAnodyneExtensions_face_one_ι
  have hinl : sq₁₂.inl ≫ sq₁₂.ι = fst _ _ ≫ ι₁ := by
    rw [sq₁₂.inl_ι]
    exact whiskerLeft_face_one_ι E
  have hinr : sq₁₂.inr ≫ sq₁₂.ι = s ▷ Δ[1] := sq₁₂.inr_ι
  -- the partial lift on `E ⊗ {1} ∪ C ⊗ Δ[1]`: `q ≫ a` at time `1`, `G' ≫ a` on `C ⊗ Δ[1]`
  let top : sq₁₂.pt ⟶ X := sq₁₂.isPushout.desc (fst _ _ ≫ q ≫ a) (G' ≫ a) (by
    change s ▷ _ ≫ fst _ _ ≫ q ≫ a = C ◁ _ ≫ G' ≫ a
    rw [whiskerRight_fst_assoc, whiskerLeft_face_one_ι, ← Category.assoc s, hG'₁]
    simp only [Category.assoc])
  have sq' : CommSq top sq₁₂.ι r (G ≫ b) := ⟨by
    apply sq₁₂.isPushout.hom_ext
    · rw [sq₁₂.isPushout.inl_desc_assoc, ← Category.assoc sq₁₂.inl, hinl]
      simp only [Category.assoc]
      rw [← Category.assoc ι₁ G, hG₁, Category.assoc, sq.w]
    · rw [sq₁₂.isPushout.inr_desc_assoc, ← Category.assoc sq₁₂.inr, hinr, ← Category.assoc, hGs,
        Category.assoc, Category.assoc, sq.w]⟩
  have := hι _ hr
  exact ⟨⟨{ l := ι₀ ≫ sq'.lift
            fac_left := by
              rw [← ι₀_comp_assoc, ← hinr, Category.assoc, sq'.fac_left,
                sq₁₂.isPushout.inr_desc, ← Category.assoc, hG'₀, Category.id_comp]
            fac_right := by
              rw [Category.assoc, sq'.fac_right, ← Category.assoc, hG₀, Category.id_comp] }⟩⟩

/-- **Deformation retracts are right anodyne.** If `s ≫ q = 𝟙 C` and `G : E ⊗ Δ[1] ⟶ E` is a
homotopy from `𝟙 E` to `q ≫ s` which is constant along `s`, then `s` is a right anodyne
extension. -/
theorem rightAnodyneExtensions_of_deformationRetract {C E : SSet.{u}} (s : C ⟶ E) (q : E ⟶ C)
    (hsq : s ≫ q = 𝟙 C) (G : E ⊗ Δ[1] ⟶ E) (hG₀ : ι₀ ≫ G = 𝟙 E) (hG₁ : ι₁ ≫ G = q ≫ s)
    (hGs : s ▷ Δ[1] ≫ G = fst _ _ ≫ s) : rightAnodyneExtensions s :=
  have : IsSplitMono s := IsSplitMono.mk' ⟨q, hsq⟩
  rightAnodyneExtensions_of_deformation s q G (fst _ _) hG₀ hG₁ hGs

end SSet
