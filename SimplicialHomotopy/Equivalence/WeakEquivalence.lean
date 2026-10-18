/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Homotopy equivalences and weak homotopy equivalences of simplicial sets

Mathlib (at the pinned commit) has Kan complexes, Kan fibrations, anodyne extensions and
simplicial homotopies `SSet.Homotopy f g` (a map `X ⊗ Δ[1] ⟶ Y`), but no class of weak
equivalences on `SSet`. We use Kerodon's definition:

* `SSet.IsHomotopyEquivalence f` : `f` has a homotopy inverse (Kerodon §3.1.6, for
  arbitrary simplicial sets; on Kan complexes this is the usual notion).
* `SSet.IsWeakHomotopyEquivalence f` : for every Kan complex `K`, the restriction
  `Fun(Y, K) ⟶ Fun(X, K)` is a homotopy equivalence (Kerodon, Definition 3.1.6.12).
* `SSet.WeaklyContractible X` : `X ⟶ ⊤` is a weak homotopy equivalence.

Further facts (all standard, all proved in this file):
* a homotopy equivalence is a weak homotopy equivalence;
* a trivial Kan fibration is a homotopy equivalence (it has a section, and the
  composite is homotopic to the identity by a lifting argument);
* if `Φ : X ⟶ X` is homotopic to `𝟙 X` and to a constant map, then `X` is weakly
  contractible.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits CartesianMonoidalCategory

open scoped Simplicial

namespace SSet

variable {X Y : SSet.{u}}

/-- `f` is a homotopy equivalence: it admits a homotopy inverse. -/
def IsHomotopyEquivalence (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, Nonempty (Homotopy (f ≫ g) (𝟙 X)) ∧ Nonempty (Homotopy (g ≫ f) (𝟙 Y))

lemma IsHomotopyEquivalence.of_isIso (f : X ⟶ Y) [IsIso f] : IsHomotopyEquivalence f :=
  ⟨inv f, ⟨by rw [IsIso.hom_inv_id]; exact RelativeMorphism.Homotopy.refl _⟩,
    ⟨by rw [IsIso.inv_hom_id]; exact RelativeMorphism.Homotopy.refl _⟩⟩

/-- `f : X ⟶ Y` is a weak homotopy equivalence if for every Kan complex `K`, the induced map
`Fun(Y, K) ⟶ Fun(X, K)` is a homotopy equivalence (Kerodon 3.1.6.12). -/
def IsWeakHomotopyEquivalence (f : X ⟶ Y) : Prop :=
  ∀ (K : SSet.{u}) [KanComplex K], IsHomotopyEquivalence ((pre f).app K)

/-- A simplicial set is weakly contractible if the map to the terminal object is a weak
homotopy equivalence. -/
def WeaklyContractible (X : SSet.{u}) : Prop :=
  IsWeakHomotopyEquivalence (terminal.from X)

/-- Constructor for `SSet.Homotopy` from a map `X ⊗ Δ[1] ⟶ Y` and its two end conditions
(the relative condition on the `⊥` subcomplex is vacuous). -/
noncomputable def Homotopy.mk' {f g : X ⟶ Y} (h : X ⊗ Δ[1] ⟶ Y)
    (h₀ : ι₀ ≫ h = f) (h₁ : ι₁ ≫ h = g) : Homotopy f g where
  h := h
  h₀ := h₀
  h₁ := h₁
  rel := by
    ext _ ⟨⟨_, hx⟩, _⟩
    simp at hx

/-- Transport a homotopy along equalities of its endpoints. -/
noncomputable def Homotopy.ofEq' {f g f' g' : X ⟶ Y} (H : Homotopy f g)
    (hf : f = f') (hg : g = g') : Homotopy f' g' :=
  Homotopy.mk' H.h (by rw [H.h₀, hf]) (by rw [H.h₁, hg])

/-- Homotopic maps induce homotopic maps on `Fun(−, K)`. -/
theorem Homotopy.pre_app {f g : X ⟶ Y} (H : Homotopy f g) (K : SSet.{u}) :
    Nonempty (Homotopy ((pre f).app K) ((pre g).app K)) := by
  -- the map `X ⊗ (Fun(Y,K) ⊗ Δ[1]) ⟶ (X ⊗ Δ[1]) ⊗ Fun(Y,K)` permuting the factors
  let σ : X ⊗ ((ihom Y).obj K ⊗ Δ[1]) ⟶ (X ⊗ Δ[1]) ⊗ (ihom Y).obj K :=
    lift (lift (fst _ _) (snd _ _ ≫ snd _ _)) (snd _ _ ≫ fst _ _)
  have hσ₀ : X ◁ ι₀ ≫ σ = ι₀ ▷ (ihom Y).obj K := by
    refine CartesianMonoidalCategory.hom_ext _ _
      (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_) ?_ <;> simp [σ]
  have hσ₁ : X ◁ ι₁ ≫ σ = ι₁ ▷ (ihom Y).obj K := by
    refine CartesianMonoidalCategory.hom_ext _ _
      (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_) ?_ <;> simp [σ]
  refine ⟨Homotopy.mk' (curry (σ ≫ H.h ▷ _ ≫ (ihom.ev Y).app K)) ?_ ?_⟩
  · rw [← curry_natural_left, ← Category.assoc, hσ₀, ← comp_whiskerRight_assoc, H.h₀,
      ← uncurry_pre, curry_uncurry]
  · rw [← curry_natural_left, ← Category.assoc, hσ₁, ← comp_whiskerRight_assoc, H.h₁,
      ← uncurry_pre, curry_uncurry]

lemma pre_app_comp {Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (K : SSet.{u}) :
    (pre (f ≫ g)).app K = (pre g).app K ≫ (pre f).app K := by
  rw [pre_map, NatTrans.comp_app]

lemma pre_app_id (K : SSet.{u}) : (pre (𝟙 X)).app K = 𝟙 _ := by
  rw [pre_id, NatTrans.id_app]

/-- A homotopy equivalence is a weak homotopy equivalence. -/
theorem IsHomotopyEquivalence.isWeakHomotopyEquivalence {f : X ⟶ Y}
    (hf : IsHomotopyEquivalence f) : IsWeakHomotopyEquivalence f := by
  obtain ⟨g, ⟨H₁⟩, ⟨H₂⟩⟩ := hf
  intro K _
  refine ⟨(pre g).app K, ?_, ?_⟩
  · obtain ⟨H⟩ := H₂.pre_app K
    exact ⟨H.ofEq' (pre_app_comp _ _ _) (pre_app_id _)⟩
  · obtain ⟨H⟩ := H₁.pre_app K
    exact ⟨H.ofEq' (pre_app_comp _ _ _) (pre_app_id _)⟩

/-- The homotopy `fst ≫ f` from `f` to itself: Mathlib's
`SSet.Subcomplex.RelativeMorphism.Homotopy.refl`, with `f` explicit. -/
noncomputable def Homotopy.refl' (f : X ⟶ Y) : Homotopy f f :=
  RelativeMorphism.Homotopy.refl _

/-- Conjugating a homotopy by maps on both sides. -/
noncomputable def Homotopy.conj {W V : SSet.{u}} {a b : X ⟶ Y} (H : Homotopy a b)
    (u : W ⟶ X) (v : Y ⟶ V) : Homotopy (u ≫ a ≫ v) (u ≫ b ≫ v) :=
  Homotopy.mk' (u ▷ _ ≫ H.h ≫ v) (by rw [ι₀_comp_assoc, H.h₀_assoc])
    (by rw [ι₁_comp_assoc, H.h₁_assoc])

/-! ### Homotopy of maps into a Kan complex is an equivalence relation

We transpose a homotopy `X ⊗ Δ[1] ⟶ Z` to a `1`-simplex of the Kan complex `Fun(X, Z)`
and use the `Λ[2, 0]`-filling property there. -/

/-- In a Kan complex, two edges with the same source can be completed to a `2`-simplex
(`Λ[2, 0]`-filling): given `a b : W _⦋1⦌` with `δ 1 a = δ 1 b`, there is `c` with
`δ 1 c = δ 0 a` and `δ 0 c = δ 0 b`. -/
lemma KanComplex.exists_edge_of_edges {W : SSet.{u}} [KanComplex W] (a b : W _⦋1⦌)
    (hab : W.δ 1 a = W.δ 1 b) :
    ∃ c : W _⦋1⦌, W.δ 1 c = W.δ 0 a ∧ W.δ 0 c = W.δ 0 b := by
  let F : ∀ (j : Fin 3) (_ : j ≠ 0), Δ[1] ⟶ W :=
    fun j _ ↦ if j = 1 then yonedaEquiv.symm b else yonedaEquiv.symm a
  have hF : horn.IsCompatible F := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk
    change stdSimplex.δ 1 ≫ yonedaEquiv.symm b = stdSimplex.δ 1 ≫ yonedaEquiv.symm a
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, hab]
  obtain ⟨φ, hφ⟩ := hF.exists_lift_of_kanComplex
  have h2 : W.δ 2 (yonedaEquiv φ) = a := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hφ 2 (by decide)]
    simp [F]
  have h1 : W.δ 1 (yonedaEquiv φ) = b := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hφ 1 (by decide)]
    simp [F]
  refine ⟨W.δ 0 (yonedaEquiv φ), ?_, ?_⟩
  · have := W.δ_comp_δ_apply (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) (yonedaEquiv φ)
    simp only [Fin.castSucc_zero, Fin.succ_one_eq_two] at this
    rw [← this, h2]
  · have := W.δ_comp_δ_self_apply (i := (0 : Fin 2)) (yonedaEquiv φ)
    simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at this
    rw [this, h1]

variable {A Z : SSet.{u}}

/-- The section `A ⟶ A ⊗ Δ[0]` of the projection. -/
noncomputable def toProdPt (A : SSet.{u}) : A ⟶ A ⊗ Δ[0] :=
  lift (𝟙 A) (const (stdSimplex.obj₀Equiv.{u}.symm 0))

@[reassoc (attr := simp)]
lemma toProdPt_fst (A : SSet.{u}) : toProdPt A ≫ fst A Δ[0] = 𝟙 A := lift_fst _ _

lemma whiskerLeft_const_zero (A : SSet.{u}) :
    A ◁ (const (stdSimplex.obj₀Equiv.{u}.symm 0) : Δ[0] ⟶ Δ[1]) = fst A Δ[0] ≫ ι₀ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [ι₀]

lemma whiskerLeft_const_one (A : SSet.{u}) :
    A ◁ (const (stdSimplex.obj₀Equiv.{u}.symm 1) : Δ[0] ⟶ Δ[1]) = fst A Δ[0] ≫ ι₁ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [ι₁]

/-- The `0`-simplex of `Fun(A, Z)` corresponding to `f : A ⟶ Z`. -/
noncomputable def ihomVertex (f : A ⟶ Z) : ((ihom A).obj Z) _⦋0⦌ :=
  yonedaEquiv (curry (fst A Δ[0] ≫ f))

lemma Homotopy.δ_one_yonedaEquiv_curry {f g : A ⟶ Z} (H : Homotopy f g) :
    ((ihom A).obj Z).δ 1 (yonedaEquiv (curry H.h)) = ihomVertex f := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← curry_natural_left, stdSimplex.δ_one_eq_const,
    whiskerLeft_const_zero, Category.assoc, H.h₀]
  rfl

lemma Homotopy.δ_zero_yonedaEquiv_curry {f g : A ⟶ Z} (H : Homotopy f g) :
    ((ihom A).obj Z).δ 0 (yonedaEquiv (curry H.h)) = ihomVertex g := by
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← curry_natural_left, stdSimplex.δ_zero_eq_const,
    whiskerLeft_const_one, Category.assoc, H.h₁]
  rfl

lemma ι₀_comp_uncurry (φ : Δ[1] ⟶ (ihom A).obj Z) :
    ι₀ ≫ uncurry φ = toProdPt A ≫ uncurry (stdSimplex.δ 1 ≫ φ) := by
  rw [uncurry_natural_left, stdSimplex.δ_one_eq_const, whiskerLeft_const_zero,
    Category.assoc, toProdPt_fst_assoc]

lemma ι₁_comp_uncurry (φ : Δ[1] ⟶ (ihom A).obj Z) :
    ι₁ ≫ uncurry φ = toProdPt A ≫ uncurry (stdSimplex.δ 0 ≫ φ) := by
  rw [uncurry_natural_left, stdSimplex.δ_zero_eq_const, whiskerLeft_const_one,
    Category.assoc, toProdPt_fst_assoc]

/-- A `1`-simplex of `Fun(A, Z)` with vertices `f` and `g` gives a homotopy `f ≃ g`. -/
noncomputable def Homotopy.ofSimplex {f g : A ⟶ Z} (e : ((ihom A).obj Z) _⦋1⦌)
    (h₁ : ((ihom A).obj Z).δ 1 e = ihomVertex f)
    (h₀ : ((ihom A).obj Z).δ 0 e = ihomVertex g) : Homotopy f g :=
  Homotopy.mk' (uncurry (yonedaEquiv.symm e))
    (by rw [ι₀_comp_uncurry, stdSimplex.δ_comp_yonedaEquiv_symm, h₁, ihomVertex,
          Equiv.symm_apply_apply, uncurry_curry, toProdPt_fst_assoc])
    (by rw [ι₁_comp_uncurry, stdSimplex.δ_comp_yonedaEquiv_symm, h₀, ihomVertex,
          Equiv.symm_apply_apply, uncurry_curry, toProdPt_fst_assoc])

/-- `Λ[2, 0]`-filling for homotopies into a Kan complex: two homotopies with the same
source give a homotopy between their targets. -/
theorem Homotopy.exists_of_kan [KanComplex Z] {f g k : A ⟶ Z}
    (H₁ : Homotopy f g) (H₂ : Homotopy f k) : Nonempty (Homotopy g k) := by
  obtain ⟨c, hc₁, hc₀⟩ := KanComplex.exists_edge_of_edges (W := (ihom A).obj Z)
    (yonedaEquiv (curry H₁.h)) (yonedaEquiv (curry H₂.h))
    (by rw [H₁.δ_one_yonedaEquiv_curry, H₂.δ_one_yonedaEquiv_curry])
  exact ⟨Homotopy.ofSimplex c (by rw [hc₁, H₁.δ_zero_yonedaEquiv_curry])
    (by rw [hc₀, H₂.δ_zero_yonedaEquiv_curry])⟩

/-- Homotopy of maps into a Kan complex is symmetric. -/
theorem Homotopy.symm_of_kan [KanComplex Z] {f g : A ⟶ Z} (H : Homotopy f g) :
    Nonempty (Homotopy g f) :=
  H.exists_of_kan (Homotopy.refl' f)

/-- Homotopy of maps into a Kan complex is transitive. -/
theorem Homotopy.trans_of_kan [KanComplex Z] {f g k : A ⟶ Z} (H₁ : Homotopy f g)
    (H₂ : Homotopy g k) : Nonempty (Homotopy f k) := by
  obtain ⟨H₁'⟩ := H₁.symm_of_kan
  exact H₁'.exists_of_kan H₂

/-- Homotopy equivalences between Kan complexes compose. -/
theorem IsHomotopyEquivalence.comp {Z : SSet.{u}} [KanComplex X] [KanComplex Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsHomotopyEquivalence f) (hg : IsHomotopyEquivalence g) :
    IsHomotopyEquivalence (f ≫ g) := by
  obtain ⟨f', ⟨Hf₁⟩, ⟨Hf₂⟩⟩ := hf
  obtain ⟨g', ⟨Hg₁⟩, ⟨Hg₂⟩⟩ := hg
  refine ⟨g' ≫ f', ?_, ?_⟩
  · have H : Homotopy ((f ≫ g) ≫ g' ≫ f') (f ≫ f') :=
      (Hg₁.conj f f').ofEq' (by simp only [Category.assoc]) (by simp)
    exact H.trans_of_kan Hf₁
  · have H : Homotopy ((g' ≫ f') ≫ f ≫ g) (g' ≫ g) :=
      (Hf₂.conj g' g).ofEq' (by simp only [Category.assoc]) (by simp)
    exact H.trans_of_kan Hg₂

/-- Weak contractibility transfers along a weak homotopy equivalence (2-out-of-3 for
the map to the point). -/
theorem weaklyContractible_of_isWeakHomotopyEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsWeakHomotopyEquivalence f) (hY : WeaklyContractible Y) :
    WeaklyContractible X := by
  have h : terminal.from X = f ≫ terminal.from Y := Subsingleton.elim _ _
  unfold WeaklyContractible
  rw [h]
  intro K _
  rw [pre_app_comp]
  exact (hY K).comp (hf K)

/-- A trivial Kan fibration (right lifting property against all monomorphisms) is a homotopy
equivalence: lifting against `⊥ ⟶ Y` gives a section `s`, and lifting against the inclusion
`X × ∂Δ[1] ⟶ X × Δ[1]` (realised as the subcomplex `range ι₀ ⊔ range ι₁`) gives a homotopy
from `f ≫ s` to `𝟙 X` over `Y`. -/
theorem isHomotopyEquivalence_of_rlp_monomorphisms {f : X ⟶ Y}
    (hf : (MorphismProperty.monomorphisms SSet.{u}).rlp f) :
    IsHomotopyEquivalence f := by
  -- a section `s` of `f`
  have sq₁ : CommSq ((Subcomplex.isInitialBot (X := Y)).to X) (⊥ : Y.Subcomplex).ι f (𝟙 Y) :=
    ⟨(Subcomplex.isInitialBot (X := Y)).hom_ext _ _⟩
  have := hf (⊥ : Y.Subcomplex).ι (MorphismProperty.monomorphisms.infer_property _)
  obtain ⟨s, hs⟩ : ∃ s : Y ⟶ X, s ≫ f = 𝟙 Y := ⟨sq₁.lift, sq₁.fac_right⟩
  -- the subcomplex `X × {0} ∪ X × {1}` of `X ⊗ Δ[1]`, as a pushout of its two pieces
  let S : (X ⊗ Δ[1]).Subcomplex := Subcomplex.range ι₀ ⊔ Subcomplex.range ι₁
  have sq : Subcomplex.BicartSq ⊥ (Subcomplex.range ι₀) (Subcomplex.range ι₁) S :=
    { sup_eq := rfl
      inf_eq := by
        refine le_antisymm ?_ bot_le
        intro n x hx
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = Opposite.op ⦋m⦌ := ⟨n.unop.len, rfl⟩
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
        have := congr_arg (fun y : (X ⊗ Δ[1]) _⦋m⦌ ↦ (y.2 : Δ[1] _⦋m⦌) 0) (ha.trans hb.symm)
        simp at this }
  obtain ⟨top, htop₀, htop₁⟩ : ∃ top : (S : SSet) ⟶ X,
      Subcomplex.homOfLE sq.le₂₄ ≫ top = (Subcomplex.range ι₀).ι ≫ fst _ _ ≫ f ≫ s ∧
      Subcomplex.homOfLE sq.le₃₄ ≫ top = (Subcomplex.range ι₁).ι ≫ fst _ _ :=
    ⟨sq.isPushout.desc _ _ ((Subcomplex.isInitialBot (X := X ⊗ Δ[1])).hom_ext _ _),
      sq.isPushout.inl_desc _ _ _, sq.isPushout.inr_desc _ _ _⟩
  have sq₂ : CommSq top S.ι f (fst _ _ ≫ f) := ⟨by
    apply sq.isPushout.hom_ext
    · rw [reassoc_of% htop₀, reassoc_of% (Subcomplex.homOfLE_ι (h := sq.le₂₄))]
      simp [hs]
    · rw [reassoc_of% htop₁, reassoc_of% (Subcomplex.homOfLE_ι (h := sq.le₃₄))]⟩
  have := hf S.ι (MorphismProperty.monomorphisms.infer_property _)
  obtain ⟨h, hh⟩ : ∃ h : X ⊗ Δ[1] ⟶ X, S.ι ≫ h = top := ⟨sq₂.lift, sq₂.fac_left⟩
  refine ⟨s, ⟨Homotopy.mk' h ?_ ?_⟩, ⟨by rw [hs]; exact Homotopy.refl' _⟩⟩
  · have e : (ι₀ : X ⟶ X ⊗ Δ[1]) =
        Subcomplex.toRange ι₀ ≫ Subcomplex.homOfLE sq.le₂₄ ≫ S.ι := by
      rw [Subcomplex.homOfLE_ι, Subcomplex.toRange_ι]
    rw [e, Category.assoc, Category.assoc, hh, htop₀]
    simp
  · have e : (ι₁ : X ⟶ X ⊗ Δ[1]) =
        Subcomplex.toRange ι₁ ≫ Subcomplex.homOfLE sq.le₃₄ ≫ S.ι := by
      rw [Subcomplex.homOfLE_ι, Subcomplex.toRange_ι]
    rw [e, Category.assoc, Category.assoc, hh, htop₁]
    simp

/-- A criterion for weak contractibility: an endomorphism `Φ`
homotopic both to the identity and to a constant map. Homotopy into a Kan complex is
an equivalence relation, so `Fun(X, K) ⟶ Fun(⊤, K) = K` is a homotopy equivalence. -/
theorem weaklyContractible_of_homotopy_id_const (Φ : X ⟶ X) (x : X _⦋0⦌)
    (α : Homotopy Φ (𝟙 X)) (γ : Homotopy Φ (const x)) : WeaklyContractible X := by
  intro K _
  refine ⟨(pre (const x : ⊤_ SSet.{u} ⟶ X)).app K, ⟨?_⟩, ?_⟩
  · have h : (const x : ⊤_ SSet.{u} ⟶ X) ≫ terminal.from X = 𝟙 _ := Subsingleton.elim _ _
    rw [← pre_app_comp, h, pre_app_id]
    exact Homotopy.refl' _
  · rw [← pre_app_comp, comp_const]
    obtain ⟨H₁⟩ := γ.pre_app K
    obtain ⟨H₂⟩ := α.pre_app K
    obtain ⟨H⟩ := H₁.exists_of_kan H₂
    exact ⟨H.ofEq' rfl (pre_app_id K)⟩

end SSet

namespace SSet

open CategoryTheory Limits

universe v

/-- Weak contractibility transfers forward along a map with the right lifting property
against monomorphisms (a trivial fibration): such a map is a homotopy equivalence, so its
homotopy inverse is a weak homotopy equivalence `Y ⟶ X`. -/
theorem weaklyContractible_of_rlp_monomorphisms {X Y : SSet.{v}} {f : X ⟶ Y}
    (hf : (MorphismProperty.monomorphisms SSet.{v}).rlp f) (hX : WeaklyContractible X) :
    WeaklyContractible Y := by
  obtain ⟨g, H₁, H₂⟩ := isHomotopyEquivalence_of_rlp_monomorphisms hf
  exact weaklyContractible_of_isWeakHomotopyEquivalence g
    (IsHomotopyEquivalence.isWeakHomotopyEquivalence ⟨f, H₂, H₁⟩) hX

end SSet
