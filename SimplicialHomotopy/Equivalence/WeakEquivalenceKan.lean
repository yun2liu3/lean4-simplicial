/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Horn.HornEdge
import SimplicialHomotopy.Equivalence.WeakEquivalence
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Homotopy equivalences of Kan complexes: 2-of-3, anodyne maps, contractibility

Further facts about `SSet.IsHomotopyEquivalence`, `SSet.IsWeakHomotopyEquivalence` and
`SSet.WeaklyContractible` (defined in `SimplicialHomotopy.Equivalence.WeakEquivalence`), all
steps in the proof of Quillen's Theorem A ([Lur09, Theorem 4.1.3.1]).

* `SSet.IsHomotopyEquivalence.of_comp_right`, `SSet.IsHomotopyEquivalence.of_comp_left` :
  2-out-of-3 (cancellation) for homotopy equivalences between Kan complexes.
* `SSet.rlp_monomorphisms_pullbackObjObjπ_of_anodyneExtensions` : the pullback-hom of an
  anodyne extension and a Kan fibration is a trivial Kan fibration, and its consequence
  `SSet.IsWeakHomotopyEquivalence.of_anodyneExtensions` : an anodyne extension is a weak
  homotopy equivalence.
* `SSet.weaklyContractible_tgt_of_isWeakHomotopyEquivalence` : weak contractibility transfers
  forward along a weak homotopy equivalence.
* `SSet.WeaklyContractible.exists_homotopy_terminal_from_comp` : into a Kan complex, a map out
  of a weakly contractible simplicial set is homotopic to one that factors through `⊤_ SSet`.
* `SSet.rlp_monomorphisms_terminal_from_of_weaklyContractible` : a weakly contractible Kan
  complex is contractible, i.e. `X ⟶ ⊤_ SSet` is a trivial Kan fibration.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits CartesianMonoidalCategory
  HomotopicalAlgebra

open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

variable {X Y Z : SSet.{u}}

/-! ### 2-out-of-3 for homotopy equivalences between Kan complexes -/

/-- 2-of-3, cancellation on the right: if `f ≫ g` and `g` are homotopy equivalences between
Kan complexes then so is `f`. The homotopy inverse of `f` is `g ≫ k` where `k` is a homotopy
inverse of `f ≫ g`. -/
theorem IsHomotopyEquivalence.of_comp_right [KanComplex X] [KanComplex Y] [KanComplex Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hfg : IsHomotopyEquivalence (f ≫ g)) (hg : IsHomotopyEquivalence g) :
    IsHomotopyEquivalence f := by
  obtain ⟨k, ⟨Hk₁⟩, ⟨Hk₂⟩⟩ := hfg
  obtain ⟨g', ⟨Hg₁⟩, ⟨Hg₂⟩⟩ := hg
  refine ⟨g ≫ k, ⟨Hk₁.ofEq' (by simp only [Category.assoc]) rfl⟩, ?_⟩
  -- `(g ≫ k ≫ f) ≫ (g ≫ g')` is homotopic both to `g ≫ k ≫ f` and to `g ≫ g' ≃ 𝟙`
  have H₁ : Homotopy ((g ≫ k ≫ f) ≫ g ≫ g') (g ≫ k ≫ f) :=
    (Hg₁.conj (g ≫ k ≫ f) (𝟙 Y)).ofEq' (by simp) (by simp)
  have H₂ : Homotopy ((g ≫ k ≫ f) ≫ g ≫ g') (g ≫ g') :=
    (Hk₂.conj g g').ofEq' (by simp only [Category.assoc]) (by simp)
  obtain ⟨H₃⟩ := H₁.exists_of_kan H₂
  obtain ⟨H⟩ := H₃.trans_of_kan Hg₁
  exact ⟨H.ofEq' (by simp only [Category.assoc]) rfl⟩

/-- 2-of-3, cancellation on the left: if `f ≫ g` and `f` are homotopy equivalences between
Kan complexes then so is `g`. The homotopy inverse of `g` is `k ≫ f` where `k` is a homotopy
inverse of `f ≫ g`. -/
theorem IsHomotopyEquivalence.of_comp_left [KanComplex X] [KanComplex Y] [KanComplex Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hfg : IsHomotopyEquivalence (f ≫ g)) (hf : IsHomotopyEquivalence f) :
    IsHomotopyEquivalence g := by
  obtain ⟨k, ⟨Hk₁⟩, ⟨Hk₂⟩⟩ := hfg
  obtain ⟨f', ⟨Hf₁⟩, ⟨Hf₂⟩⟩ := hf
  refine ⟨k ≫ f, ?_, ⟨Hk₂.ofEq' (by simp only [Category.assoc]) rfl⟩⟩
  -- `(f' ≫ f) ≫ (g ≫ k ≫ f)` is homotopic both to `g ≫ k ≫ f` and to `f' ≫ f ≃ 𝟙`
  have H₁ : Homotopy ((f' ≫ f) ≫ g ≫ k ≫ f) (g ≫ k ≫ f) :=
    (Hf₂.conj (𝟙 Y) (g ≫ k ≫ f)).ofEq' (by simp) (by simp)
  have H₂ : Homotopy ((f' ≫ f) ≫ g ≫ k ≫ f) (f' ≫ f) :=
    (Hk₁.conj f' f).ofEq' (by simp only [Category.assoc]) (by simp)
  obtain ⟨H₃⟩ := H₁.exists_of_kan H₂
  exact H₃.trans_of_kan Hf₂

/-! ### Anodyne extensions are weak homotopy equivalences -/

section

variable {E B : SSet.{u}} {i : X ⟶ Y} {p : E ⟶ B}

/-- The pullback-hom of an anodyne extension `i` and a Kan fibration `p` is a trivial Kan
fibration (the "other half" of Mathlib's `SSet.fibration_pullbackObjObjπ`): lifting
`∂Δ[n] ⟶ Δ[n]` against `sq₁₃.π` transposes to lifting the pushout-product
`i □ ∂Δ[n].ι`, which is anodyne, against `p`. -/
lemma rlp_monomorphisms_pullbackObjObjπ_of_anodyneExtensions (hi : anodyneExtensions i)
    [Fibration p] (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp sq₁₃.π := by
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i ∂Δ[n].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂ sq₁₃]
  exact anodyneExtensions_pushoutObjObjι' sq₁₂ hi _
    (by rwa [← HomotopicalAlgebra.fibration_iff])

end

/-- An anodyne extension is a weak homotopy equivalence: for a Kan complex `K`,
`(pre f).app K : Fun(Y, K) ⟶ Fun(X, K)` has the right lifting property against monomorphisms,
hence is a homotopy equivalence. -/
theorem IsWeakHomotopyEquivalence.of_anodyneExtensions {f : X ⟶ Y}
    (hf : anodyneExtensions f) : IsWeakHomotopyEquivalence f := by
  intro K _
  exact isHomotopyEquivalence_of_rlp_monomorphisms
    (rlp_monomorphisms_pullbackObjObjπ_of_anodyneExtensions hf
      (Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom f (terminal.from K)
        terminalIsTerminal))

/-! ### Forward transfer of weak contractibility -/

/-- Weak contractibility transfers forward along a weak homotopy equivalence (2-out-of-3 for
the map to the point, cancellation on the right). -/
theorem weaklyContractible_tgt_of_isWeakHomotopyEquivalence {f : X ⟶ Y}
    (hf : IsWeakHomotopyEquivalence f) (hX : WeaklyContractible X) : WeaklyContractible Y := by
  have h : terminal.from X = f ≫ terminal.from Y := Subsingleton.elim _ _
  intro K _
  have hXK := hX K
  rw [h, pre_app_comp] at hXK
  exact IsHomotopyEquivalence.of_comp_right hXK (hf K)

/-! ### A weakly contractible Kan complex is contractible -/

/-- Every vertex of `Fun(A, Z)` is `ihomVertex φ` for some `φ : A ⟶ Z`. -/
lemma exists_eq_ihomVertex {A : SSet.{u}} (w : ((ihom A).obj Z) _⦋0⦌) :
    ∃ φ : A ⟶ Z, w = ihomVertex φ := by
  refine ⟨toProdPt A ≫ uncurry (yonedaEquiv.symm w), ?_⟩
  have h : fst A Δ[0] ≫ toProdPt A = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · exact stdSimplex.ext₀
  rw [ihomVertex, ← Category.assoc, h, Category.id_comp, curry_uncurry, Equiv.apply_symm_apply]

/-- `ihomVertex` is natural in the source: `(pre f).app Z` sends the vertex `φ` to `f ≫ φ`. -/
lemma pre_app_ihomVertex {A B : SSet.{u}} (f : B ⟶ A) (φ : A ⟶ Z) :
    ((pre f).app Z).app _ (ihomVertex φ) = ihomVertex (f ≫ φ) := by
  rw [ihomVertex, ihomVertex, ← yonedaEquiv_comp, curry_pre_app, ← Category.assoc,
    whiskerRight_fst, Category.assoc]

/-- The inclusion `X ⊗ {0} ⟶ X ⊗ Δ[1]` factors through `ι₀`. -/
lemma whiskerLeft_face_zero_ι (X : SSet.{u}) :
    X ◁ (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι = fst _ _ ≫ ι₀ := by
  rw [← Category.id_comp (stdSimplex.face {0}).ι,
    ← (stdSimplex.faceSingletonIso (0 : Fin 2)).inv_hom_id, Category.assoc,
    stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ, stdSimplex.δ_one_eq_const,
    MonoidalCategory.whiskerLeft_comp, whiskerLeft_const_zero, ← Category.assoc,
    whiskerLeft_fst]

/-- If `X` is a Kan complex and `𝟙 X` is homotopic to a map factoring through the point, then
every `b : ∂Δ[n] ⟶ X` extends to `Δ[n]`: the map `b ▷ Δ[1] ≫ h.h` on `∂Δ[n] ⊗ Δ[1]` is constant
at time `0`, so it glues with the constant map on `Δ[n] ⊗ {0}`; the inclusion of
`Δ[n] ⊗ {0} ∪ ∂Δ[n] ⊗ Δ[1]` into `Δ[n] ⊗ Δ[1]` is anodyne, and the time-`1` restriction of an
extension to `Δ[n] ⊗ Δ[1]` extends `b`. -/
lemma hasLiftingProperty_boundary_ι_terminal_from [KanComplex X] {φ : ⊤_ SSet.{u} ⟶ X}
    (h : Homotopy (terminal.from X ≫ φ) (𝟙 X)) (n : ℕ) :
    HasLiftingProperty ∂Δ[n].ι (terminal.from X) := by
  have hT : anodyneExtensions (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
    rw [← horn_one_zero_eq_face]
    exact anodyneExtensions.horn_ι 0
  constructor
  intro b t sq
  have hglue : ∂Δ[n].ι ▷ ((stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ≫
        terminal.from _ ≫ φ =
      (∂Δ[n] : SSet.{u}) ◁ (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι ≫
        b ▷ Δ[1] ≫ h.h := by
    rw [whisker_exchange_assoc, whiskerLeft_face_zero_ι, Category.assoc, h.h₀]
    simp only [← Category.assoc]
    congr 1
    exact Subsingleton.elim _ _
  obtain ⟨top, -, htop₂⟩ : ∃ top : ((∂Δ[n]).unionProd
        (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) : SSet.{u}) ⟶ X,
      Subcomplex.unionProd.ι₁ _ _ ≫ top = terminal.from _ ≫ φ ∧
      Subcomplex.unionProd.ι₂ _ _ ≫ top = b ▷ Δ[1] ≫ h.h :=
    ⟨(Subcomplex.unionProd.isPushout _ _).desc _ _ hglue,
      (Subcomplex.unionProd.isPushout _ _).inl_desc _ _ _,
      (Subcomplex.unionProd.isPushout _ _).inr_desc _ _ _⟩
  have sq' : CommSq top ((∂Δ[n]).unionProd
      (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι (terminal.from X)
      (terminal.from _) := ⟨Subsingleton.elim _ _⟩
  have := anodyneExtensions_unionProd_ι ∂Δ[n] _ hT _
    (by rwa [← HomotopicalAlgebra.fibration_iff] : (fibrations _) (terminal.from X))
  obtain ⟨l, hl⟩ : ∃ l : Δ[n] ⊗ Δ[1] ⟶ X, ((∂Δ[n]).unionProd
      (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι ≫ l = top :=
    ⟨sq'.lift, sq'.fac_left⟩
  exact ⟨⟨{ l := ι₁ ≫ l
            fac_left := by
              rw [← ι₁_comp_assoc, ← Subcomplex.unionProd.ι₂_ι_assoc, hl, htop₂,
                ι₁_comp_assoc, h.h₁, Category.comp_id]
            fac_right := Subsingleton.elim _ _ }⟩⟩

/-- Into a Kan complex `K`, every map out of a weakly contractible `X` is homotopic to one that
factors through the terminal object: evaluate the homotopy
`g ≫ (pre (terminal.from X)).app K ≃ 𝟙`, where `g` is a homotopy inverse of
`(pre (terminal.from X)).app K`, at the vertex `φ` of `Fun(X, K)`. -/
theorem WeaklyContractible.exists_homotopy_terminal_from_comp {X K : SSet.{u}} [KanComplex K]
    (hX : WeaklyContractible X) (φ : X ⟶ K) :
    ∃ φ' : ⊤_ SSet.{u} ⟶ K, Nonempty (Homotopy (terminal.from X ≫ φ') φ) := by
  obtain ⟨g, ⟨_⟩, ⟨H⟩⟩ := hX K
  obtain ⟨φ', hφ'⟩ := exists_eq_ihomVertex (g.app _ (ihomVertex φ))
  refine ⟨φ', ⟨?_⟩⟩
  let e : ((ihom X).obj K) _⦋1⦌ :=
    yonedaEquiv (lift (const (ihomVertex φ)) (𝟙 Δ[1]) ≫ H.h)
  have he₁ : ((ihom X).obj K).δ 1 e = ihomVertex (terminal.from X ≫ φ') := by
    have h1 : (stdSimplex.δ 1 : Δ[0] ⟶ Δ[1]) ≫ lift (const (ihomVertex φ)) (𝟙 Δ[1]) =
        const (ihomVertex φ) ≫ ι₀ := by
      rw [comp_lift, comp_const, Category.comp_id, stdSimplex.δ_one_eq_const, ι₀, comp_lift,
        comp_const, Category.comp_id]
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, h1, Category.assoc, H.h₀,
      yonedaEquiv_comp, yonedaEquiv_const]
    change ((pre (terminal.from X)).app K).app _ (g.app _ (ihomVertex φ)) = _
    rw [hφ', pre_app_ihomVertex]
  have he₀ : ((ihom X).obj K).δ 0 e = ihomVertex φ := by
    have h0 : (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]) ≫ lift (const (ihomVertex φ)) (𝟙 Δ[1]) =
        const (ihomVertex φ) ≫ ι₁ := by
      rw [comp_lift, comp_const, Category.comp_id, stdSimplex.δ_zero_eq_const, ι₁, comp_lift,
        comp_const, Category.comp_id]
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, h0, Category.assoc, H.h₁,
      Category.comp_id, yonedaEquiv_const]
  exact Homotopy.ofSimplex e he₁ he₀

/-- A weakly contractible Kan complex is contractible: `X ⟶ ⊤_ SSet` has the right lifting
property against all monomorphisms. -/
theorem rlp_monomorphisms_terminal_from_of_weaklyContractible [KanComplex X]
    (hX : WeaklyContractible X) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from X) := by
  -- a homotopy `h` from a map `X ⟶ ⊤ ⟶ X` to `𝟙 X`
  obtain ⟨φ, ⟨h⟩⟩ := hX.exists_homotopy_terminal_from_comp (𝟙 X)
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  exact hasLiftingProperty_boundary_ι_terminal_from h n

end SSet
