/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Cofinal.Cofinal
import SimplicialHomotopy.Anodyne.RightAnodyne
import SimplicialHomotopy.Fibration.Fiber

/-!
# Basic facts about cofinal maps

The three formal facts about cofinal maps (`SSet.IsCofinal`, [Lur09, 4.1.1.1]) needed to
assemble Joyal's Theorem A from a factorisation `p = i ≫ q` of a map into a right anodyne
extension `i` followed by a right fibration `q` with the right lifting property against
monomorphisms:

* `SSet.isCofinal_of_rightAnodyneExtensions`: right anodyne maps are cofinal, because
  restriction along a right anodyne map is a trivial fibration on relative mapping spaces
  (`SSet.rlp_monomorphisms_relMapRestrict_of_rightAnodyneExtensions`, a base change of the
  pullback-hom of `i` and the right fibration, [Lur09, 2.1.2.9]);
* `SSet.isCofinal_of_rlp_monomorphisms`: a right fibration `q` with the right lifting
  property against monomorphisms is cofinal. A section `s` of `q` and a fibrewise homotopy
  `G` from `q ≫ s` to `𝟙` (both obtained by lifting) give a homotopy inverse of
  `Map_C(C, X) ⟶ Map_C(Z, X)`, precomposition with `s`; the homotopy `G_t ≫ φ` is written
  down explicitly (`SSet.preHomotopy`), so no Kan-complex structure is needed here;
* `SSet.isCofinal_comp_of_rightAnodyneExtensions`: the composite of a right anodyne map with
  a cofinal map is cofinal, by the composition law `SSet.relMapRestrict_comp` and the
  composition of homotopy equivalences between Kan complexes. The relative mapping spaces
  `Map_B(A, X)` are Kan complexes when `X ⟶ B` is a right fibration
  (`SSet.instKanComplexRelMap`), by the same argument as for fibers over a vertex.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits CartesianMonoidalCategory

open scoped Simplicial

namespace SSet

/-! ### A small well-typed API for `relMap`

`relMap f q` is a `def`, so the projections of the underlying pullback are not well typed at
reducible transparency once `relMap` is unfolded; we record them, together with the universal
property, as lemmas stated at the type `relMap f q`. -/

section API

variable {A B X : SSet.{u}} (f : A ⟶ B) (q : X ⟶ B)

/-- The first projection `Map_B(A, X) ⟶ Fun(A, X)`. -/
noncomputable def relMapFst : relMap f q ⟶ (ihom A).obj X := pullback.fst _ _

/-- The second projection `Map_B(A, X) ⟶ 𝟙_ SSet`. -/
noncomputable def relMapSnd : relMap f q ⟶ 𝟙_ SSet.{u} := pullback.snd _ _

@[reassoc]
lemma relMapFst_map : relMapFst f q ≫ (ihom A).map q = relMapSnd f q ≫ pointOf f :=
  pullback.condition

lemma relMap_hom_ext {W : SSet.{u}} {a b : W ⟶ relMap f q}
    (h₁ : a ≫ relMapFst f q = b ≫ relMapFst f q) (h₂ : a ≫ relMapSnd f q = b ≫ relMapSnd f q) :
    a = b :=
  pullback.hom_ext h₁ h₂

/-- A map into `Map_B(A, X)` from its two components. -/
noncomputable def relMapLift {W : SSet.{u}} (a : W ⟶ (ihom A).obj X) (b : W ⟶ 𝟙_ SSet.{u})
    (h : a ≫ (ihom A).map q = b ≫ pointOf f) : W ⟶ relMap f q :=
  pullback.lift a b h

@[reassoc (attr := simp)]
lemma relMapLift_fst {W : SSet.{u}} (a : W ⟶ (ihom A).obj X) (b : W ⟶ 𝟙_ SSet.{u})
    (h : a ≫ (ihom A).map q = b ≫ pointOf f) : relMapLift f q a b h ≫ relMapFst f q = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relMapLift_snd {W : SSet.{u}} (a : W ⟶ (ihom A).obj X) (b : W ⟶ 𝟙_ SSet.{u})
    (h : a ≫ (ihom A).map q = b ≫ pointOf f) : relMapLift f q a b h ≫ relMapSnd f q = b :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma relMapRestrict_fst {A' : SSet.{u}} (p : A' ⟶ A) :
    relMapRestrict p f q ≫ relMapFst (p ≫ f) q = relMapFst f q ≫ (pre p).app X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relMapRestrict_snd {A' : SSet.{u}} (p : A' ⟶ A) :
    relMapRestrict p f q ≫ relMapSnd (p ≫ f) q = relMapSnd f q :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

end API

/-! ### The composition law for `relMapRestrict` -/

/-- Composition law for restriction of relative mapping spaces. -/
lemma relMapRestrict_comp {S Z C B X : SSet.{u}} (i : S ⟶ Z) (p : Z ⟶ C) (f : C ⟶ B)
    (r : X ⟶ B) :
    relMapRestrict (i ≫ p) f r = relMapRestrict p f r ≫ relMapRestrict i (p ≫ f) r := by
  -- the two sides land in `relMap ((i ≫ p) ≫ f) r` and `relMap (i ≫ p ≫ f) r`, which are
  -- definitionally equal; respell the projections so that each side is well typed on its own
  apply relMap_hom_ext
  · change _ = (relMapRestrict p f r ≫ relMapRestrict i (p ≫ f) r) ≫ relMapFst (i ≫ p ≫ f) r
    rw [relMapRestrict_fst, Category.assoc, relMapRestrict_fst, relMapRestrict_fst_assoc,
      pre_app_comp]
  · change _ = (relMapRestrict p f r ≫ relMapRestrict i (p ≫ f) r) ≫ relMapSnd (i ≫ p ≫ f) r
    rw [relMapRestrict_snd, Category.assoc, relMapRestrict_snd, relMapRestrict_snd]

/-! ### Relative mapping spaces over a right fibration are Kan complexes -/

section KanRelMap

variable {E B : SSet.{u}} (q : E ⟶ B) (t : 𝟙_ SSet.{u} ⟶ B)

/-- The fiber of a right fibration over a point `t : 𝟙_ SSet ⟶ B` is a right fibration
over the point (generalising the instance for `fiberProj q b` of `Fiber.lean` to a point that
is not of the form `const b`). -/
instance [RightFibration q] : RightFibration (pullback.snd q t) :=
  ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback q t) (mem_rightFibrations q)⟩

instance [RightFibration q] : Quasicategory (pullback q t) :=
  quasicategory_of_innerFibration (pullback.snd q t)

/-- The fiber of a right fibration over a point is a Kan complex (Kerodon 019D + 019K). -/
instance [RightFibration q] : KanComplex (pullback q t) :=
  kanComplex_of_isEquiv_edges (pullback q t)
    (fun e ↦ SimplicialHomotopy.isEquiv_of_rightFibration (pullback.snd q t)
      (KanComplex.isEquiv_edge (e.map (pullback.snd q t))))
    fillOuterHornOfIsEquiv

end KanRelMap

/-- `Map_B(A, X)` is a Kan complex when `r : X ⟶ B` is a right fibration: it is the fiber of
the right fibration `(ihom A).map r` over the point `pointOf f`. -/
instance instKanComplexRelMap {A B X : SSet.{u}} (f : A ⟶ B) (r : X ⟶ B) [RightFibration r] :
    KanComplex (relMap f r) :=
  inferInstanceAs (KanComplex (pullback ((ihom A).map r) (pointOf f)))

/-! ### Restriction along a right anodyne map is a trivial fibration -/

/-- The pullback-hom of a right anodyne extension `i` and a right fibration `r` is a trivial
fibration (the "other half" of `SSet.rightFibration_pullbackObjObjπ`): lifting `∂Δ[n] ⟶ Δ[n]`
against `sq₁₃.π` transposes to lifting the pushout-product `i □ ∂Δ[n].ι`, which is right
anodyne, against `r`. -/
lemma rlp_monomorphisms_pullbackObjObjπ_of_rightAnodyneExtensions {S Z X C : SSet.{u}}
    {i : S ⟶ Z} (hi : rightAnodyneExtensions i) {r : X ⟶ C} [RightFibration r]
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i r) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp sq₁₃.π := by
  rw [rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i ∂Δ[n].ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂ sq₁₃]
  exact rightAnodyneExtensions_pushoutObjObjι' sq₁₂ hi _ (mem_rightFibrations r)

/-- Restriction along a right anodyne map is a trivial fibration on relative mapping spaces
over any base: `relMapRestrict i f r` is a base change of the pullback-hom of `i` and `r`, and
we transport the lifting problems directly. -/
theorem rlp_monomorphisms_relMapRestrict_of_rightAnodyneExtensions {S Z C X : SSet.{u}}
    {i : S ⟶ Z} (hi : rightAnodyneExtensions i) (f : Z ⟶ C) (r : X ⟶ C) [RightFibration r] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (relMapRestrict i f r) := by
  intro K L m hm
  -- the pullback-hom `π` of `i` and `r`, repackaged with its projections stated at the types
  -- `(ihom Z).obj X` and `pullback ((ihom S).map r) ((pre i).app C)` (definitionally those of
  -- `Functor.PullbackObjObj.ofHasPullback internalHom i r`, but not reducibly so)
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i r
  obtain ⟨π, hπf, hπs, hπ⟩ : ∃ π : (ihom Z).obj X ⟶ pullback ((ihom S).map r) ((pre i).app C),
      π ≫ pullback.fst _ _ = (pre i).app X ∧ π ≫ pullback.snd _ _ = (ihom Z).map r ∧
      HasLiftingProperty m π :=
    ⟨sq₁₃.π, sq₁₃.π_fst, sq₁₃.π_snd,
      rlp_monomorphisms_pullbackObjObjπ_of_rightAnodyneExtensions hi sq₁₃ m hm⟩
  constructor
  intro u v sq
  -- the square against `π`: its bottom map has constant second component `pointOf f`
  have hv : (v ≫ relMapFst (i ≫ f) r) ≫ (ihom S).map r =
      (v ≫ relMapSnd (i ≫ f) r ≫ pointOf f) ≫ (pre i).app C := by
    rw [Category.assoc, relMapFst_map, Category.assoc, Category.assoc, pointOf_comp_pre]
  have hu : u ≫ relMapSnd f r = m ≫ v ≫ relMapSnd (i ≫ f) r := by
    rw [← relMapRestrict_snd f r i, reassoc_of% sq.w]
  have sq' : CommSq (u ≫ relMapFst f r) m π
      (pullback.lift (v ≫ relMapFst (i ≫ f) r) (v ≫ relMapSnd (i ≫ f) r ≫ pointOf f) hv) :=
    ⟨by
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [hπf, pullback.lift_fst, ← relMapRestrict_fst f r i, reassoc_of% sq.w]
      · simp only [Category.assoc]
        rw [hπs, pullback.lift_snd, relMapFst_map, reassoc_of% hu]⟩
  obtain ⟨w, hw₁, hw₂⟩ : ∃ w : L ⟶ (ihom Z).obj X, m ≫ w = u ≫ relMapFst f r ∧
      w ≫ π = pullback.lift _ _ hv := ⟨sq'.lift, sq'.fac_left, sq'.fac_right⟩
  have hwf := hw₂ =≫ pullback.fst _ _
  rw [Category.assoc, hπf, pullback.lift_fst] at hwf
  have hws := hw₂ =≫ pullback.snd _ _
  rw [Category.assoc, hπs, pullback.lift_snd] at hws
  exact ⟨⟨{ l := relMapLift f r w (v ≫ relMapSnd (i ≫ f) r)
              (hws.trans (Category.assoc _ _ _).symm)
            fac_left := by
              apply relMap_hom_ext
              · rw [Category.assoc, relMapLift_fst, hw₁]
              · rw [Category.assoc, relMapLift_snd, hu]
            fac_right := by
              apply relMap_hom_ext
              · rw [Category.assoc, relMapRestrict_fst, relMapLift_fst_assoc, hwf]
              · rw [Category.assoc, relMapRestrict_snd, relMapLift_snd] }⟩⟩

/-- Restriction `Map_C(Z, X) ⟶ Map_C(S, X)` along a right anodyne extension `i : S ⟶ Z` is a
homotopy equivalence for every right fibration `r : X ⟶ C`, being a trivial fibration. -/
theorem isHomotopyEquivalence_relMapRestrict_of_rightAnodyneExtensions {S Z C X : SSet.{u}}
    {i : S ⟶ Z} (hi : rightAnodyneExtensions i) (f : Z ⟶ C) (r : X ⟶ C) [RightFibration r] :
    IsHomotopyEquivalence (relMapRestrict i f r) :=
  isHomotopyEquivalence_of_rlp_monomorphisms
    (rlp_monomorphisms_relMapRestrict_of_rightAnodyneExtensions hi f r)

/-- Right anodyne maps are cofinal ([Lur09, Proposition 4.1.1.3(4)], the "if" direction). -/
theorem isCofinal_of_rightAnodyneExtensions {S Z : SSet.{u}} {i : S ⟶ Z}
    (hi : rightAnodyneExtensions i) : IsCofinal i :=
  fun _ r _ ↦ isHomotopyEquivalence_relMapRestrict_of_rightAnodyneExtensions hi (𝟙 _) r

/-! ### Precomposition with a homotopy on internal homs -/

section PreHomotopy

variable {Z W : SSet.{u}}

/-- The permutation `Z ⊗ (F ⊗ Δ[1]) ⟶ (Z ⊗ Δ[1]) ⊗ F`. -/
noncomputable def swapMid (Z F : SSet.{u}) : Z ⊗ (F ⊗ Δ[1]) ⟶ (Z ⊗ Δ[1]) ⊗ F :=
  lift (lift (fst _ _) (snd _ _ ≫ snd _ _)) (snd _ _ ≫ fst _ _)

lemma whiskerLeft_ι₀_swapMid (Z F : SSet.{u}) : Z ◁ ι₀ ≫ swapMid Z F = ι₀ ▷ F := by
  refine CartesianMonoidalCategory.hom_ext _ _
    (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_) ?_ <;> simp [swapMid]

lemma whiskerLeft_ι₁_swapMid (Z F : SSet.{u}) : Z ◁ ι₁ ≫ swapMid Z F = ι₁ ▷ F := by
  refine CartesianMonoidalCategory.hom_ext _ _
    (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_) ?_ <;> simp [swapMid]

@[reassoc]
lemma whiskerLeft_whiskerRight_swapMid {F F' : SSet.{u}} (Z : SSet.{u}) (m : F ⟶ F') :
    Z ◁ (m ▷ Δ[1]) ≫ swapMid Z F' = swapMid Z F ≫ (Z ⊗ Δ[1]) ◁ m := by
  refine CartesianMonoidalCategory.hom_ext _ _
    (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_) ?_ <;> simp [swapMid]

/-- Precomposition with a homotopy `G : Z ⊗ Δ[1] ⟶ W`, as a homotopy
`Fun(W, X) ⊗ Δ[1] ⟶ Fun(Z, X)` from `(pre (ι₀ ≫ G)).app X` to `(pre (ι₁ ≫ G)).app X`. -/
noncomputable def preHomotopy (G : Z ⊗ Δ[1] ⟶ W) (X : SSet.{u}) :
    (ihom W).obj X ⊗ Δ[1] ⟶ (ihom Z).obj X :=
  curry (swapMid Z _ ≫ G ▷ _ ≫ (ihom.ev W).app X)

lemma ι₀_preHomotopy (G : Z ⊗ Δ[1] ⟶ W) (X : SSet.{u}) :
    ι₀ ≫ preHomotopy G X = (pre (ι₀ ≫ G)).app X := by
  rw [preHomotopy, ← curry_natural_left, ← Category.assoc, whiskerLeft_ι₀_swapMid,
    ← comp_whiskerRight_assoc, ← uncurry_pre, curry_uncurry]

lemma ι₁_preHomotopy (G : Z ⊗ Δ[1] ⟶ W) (X : SSet.{u}) :
    ι₁ ≫ preHomotopy G X = (pre (ι₁ ≫ G)).app X := by
  rw [preHomotopy, ← curry_natural_left, ← Category.assoc, whiskerLeft_ι₁_swapMid,
    ← comp_whiskerRight_assoc, ← uncurry_pre, curry_uncurry]

/-- `preHomotopy` is natural in the target. -/
@[reassoc]
lemma preHomotopy_map (G : Z ⊗ Δ[1] ⟶ W) {X X' : SSet.{u}} (r : X ⟶ X') :
    preHomotopy G X ≫ (ihom Z).map r = (ihom W).map r ▷ Δ[1] ≫ preHomotopy G X' := by
  rw [preHomotopy, preHomotopy, ← curry_natural_right, ← curry_natural_left]
  congr 1

/-- If `G` is a homotopy over `C` (`G ≫ f = fst ≫ f'`), precomposition with `G` fixes the
point `pointOf f`. -/
lemma pointOf_whiskerRight_preHomotopy (G : Z ⊗ Δ[1] ⟶ W) {C : SSet.{u}} (f : W ⟶ C)
    (f' : Z ⟶ C) (hG : G ≫ f = fst _ _ ≫ f') :
    pointOf f ▷ Δ[1] ≫ preHomotopy G C = fst _ _ ≫ pointOf f' := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, preHomotopy, uncurry_curry,
    whiskerLeft_whiskerRight_swapMid_assoc, whisker_exchange_assoc, ← uncurry_eq, pointOf,
    pointOf, uncurry_curry, uncurry_curry, rightUnitor_naturality_assoc, hG]
  simp [swapMid, rightUnitor_hom]

end PreHomotopy

/-! ### A trivial fibration is cofinal -/

/-- A map with the right lifting property against monomorphisms has a section. -/
lemma exists_section_of_rlp_monomorphisms {Z C : SSet.{u}} {q : Z ⟶ C}
    (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q) : ∃ s : C ⟶ Z, s ≫ q = 𝟙 C := by
  have sq : CommSq ((Subcomplex.isInitialBot (X := C)).to Z) (⊥ : C.Subcomplex).ι q (𝟙 C) :=
    ⟨(Subcomplex.isInitialBot (X := C)).hom_ext _ _⟩
  have := hq (⊥ : C.Subcomplex).ι (MorphismProperty.monomorphisms.infer_property _)
  exact ⟨sq.lift, sq.fac_right⟩

/-- A map `q` with the right lifting property against monomorphisms and a section `s` admits a
fibrewise homotopy from `q ≫ s` to `𝟙`, by lifting against `Z ⊗ ∂Δ[1] ⟶ Z ⊗ Δ[1]` (realised
as the subcomplex `range ι₀ ⊔ range ι₁`, as in
`SSet.isHomotopyEquivalence_of_rlp_monomorphisms`). -/
lemma exists_homotopy_of_rlp_monomorphisms {Z C : SSet.{u}} {q : Z ⟶ C}
    (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q) {s : C ⟶ Z} (hs : s ≫ q = 𝟙 C) :
    ∃ G : Z ⊗ Δ[1] ⟶ Z, ι₀ ≫ G = q ≫ s ∧ ι₁ ≫ G = 𝟙 Z ∧ G ≫ q = fst _ _ ≫ q := by
  let S : (Z ⊗ Δ[1]).Subcomplex := Subcomplex.range ι₀ ⊔ Subcomplex.range ι₁
  have sq : Subcomplex.BicartSq ⊥ (Subcomplex.range ι₀) (Subcomplex.range ι₁) S :=
    { sup_eq := rfl
      inf_eq := by
        refine le_antisymm ?_ bot_le
        intro n x hx
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = Opposite.op ⦋m⦌ := ⟨n.unop.len, rfl⟩
        obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
        have := congr_arg (fun y : (Z ⊗ Δ[1]) _⦋m⦌ ↦ (y.2 : Δ[1] _⦋m⦌) 0) (ha.trans hb.symm)
        simp at this }
  obtain ⟨top, htop₀, htop₁⟩ : ∃ top : (S : SSet) ⟶ Z,
      Subcomplex.homOfLE sq.le₂₄ ≫ top = (Subcomplex.range ι₀).ι ≫ fst _ _ ≫ q ≫ s ∧
      Subcomplex.homOfLE sq.le₃₄ ≫ top = (Subcomplex.range ι₁).ι ≫ fst _ _ :=
    ⟨sq.isPushout.desc _ _ ((Subcomplex.isInitialBot (X := Z ⊗ Δ[1])).hom_ext _ _),
      sq.isPushout.inl_desc _ _ _, sq.isPushout.inr_desc _ _ _⟩
  have sq₂ : CommSq top S.ι q (fst _ _ ≫ q) := ⟨by
    apply sq.isPushout.hom_ext
    · rw [reassoc_of% htop₀, reassoc_of% (Subcomplex.homOfLE_ι (h := sq.le₂₄))]
      simp [hs]
    · rw [reassoc_of% htop₁, reassoc_of% (Subcomplex.homOfLE_ι (h := sq.le₃₄))]⟩
  have := hq S.ι (MorphismProperty.monomorphisms.infer_property _)
  refine ⟨sq₂.lift, ?_, ?_, sq₂.fac_right⟩
  · have e : (ι₀ : Z ⟶ Z ⊗ Δ[1]) =
        Subcomplex.toRange ι₀ ≫ Subcomplex.homOfLE sq.le₂₄ ≫ S.ι := by
      rw [Subcomplex.homOfLE_ι, Subcomplex.toRange_ι]
    rw [e, Category.assoc, Category.assoc, sq₂.fac_left, htop₀]
    simp
  · have e : (ι₁ : Z ⟶ Z ⊗ Δ[1]) =
        Subcomplex.toRange ι₁ ≫ Subcomplex.homOfLE sq.le₃₄ ≫ S.ι := by
      rw [Subcomplex.homOfLE_ι, Subcomplex.toRange_ι]
    rw [e, Category.assoc, Category.assoc, sq₂.fac_left, htop₁]
    simp

/-- A right fibration with the right lifting property against monomorphisms is cofinal.
For a right fibration `r : X ⟶ C`, precomposition with a section `s` of `q` is a strict
retraction of `Map_C(C, X) ⟶ Map_C(Z, X)`, and a fibrewise homotopy `G` from `q ≫ s` to `𝟙 Z`
induces, by precomposition, a homotopy from the other composite to the identity. -/
theorem isCofinal_of_rlp_monomorphisms {Z C : SSet.{u}} (q : Z ⟶ C) [RightFibration q]
    (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q) : IsCofinal q := by
  obtain ⟨s, hs⟩ := exists_section_of_rlp_monomorphisms hq
  obtain ⟨G, hG₀, hG₁, hGq⟩ := exists_homotopy_of_rlp_monomorphisms hq hs
  intro X r _
  -- the homotopy inverse: precomposition with the section `s`
  have hg : (relMapFst (q ≫ 𝟙 C) r ≫ (pre s).app X) ≫ (ihom C).map r =
      relMapSnd (q ≫ 𝟙 C) r ≫ pointOf (𝟙 C) := by
    rw [Category.assoc, pre_comm_ihom_map, relMapFst_map_assoc, pointOf_comp_pre,
      ← Category.assoc s, hs, Category.id_comp]
  let g : relMap (q ≫ 𝟙 C) r ⟶ relMap (𝟙 C) r :=
    relMapLift (𝟙 C) r (relMapFst (q ≫ 𝟙 C) r ≫ (pre s).app X) (relMapSnd (q ≫ 𝟙 C) r) hg
  -- the homotopy `(φ, t) ↦ G_t ≫ φ` from `g ≫ relMapRestrict q (𝟙 C) r` to `𝟙`
  have hH : (relMapFst (q ≫ 𝟙 C) r ▷ Δ[1] ≫ preHomotopy G X) ≫ (ihom Z).map r =
      (fst _ _ ≫ relMapSnd (q ≫ 𝟙 C) r) ≫ pointOf (q ≫ 𝟙 C) := by
    rw [Category.assoc, preHomotopy_map, ← comp_whiskerRight_assoc, relMapFst_map,
      comp_whiskerRight_assoc, pointOf_whiskerRight_preHomotopy G (q ≫ 𝟙 C) (q ≫ 𝟙 C)
        (by rw [← Category.assoc, hGq, Category.assoc]),
      whiskerRight_fst_assoc, Category.assoc]
  let H : relMap (q ≫ 𝟙 C) r ⊗ Δ[1] ⟶ relMap (q ≫ 𝟙 C) r :=
    relMapLift (q ≫ 𝟙 C) r (relMapFst (q ≫ 𝟙 C) r ▷ Δ[1] ≫ preHomotopy G X)
      (fst _ _ ≫ relMapSnd (q ≫ 𝟙 C) r) hH
  have hρg : relMapRestrict q (𝟙 C) r ≫ g = 𝟙 _ := by
    apply relMap_hom_ext
    · rw [Category.assoc, relMapLift_fst, relMapRestrict_fst_assoc, ← pre_app_comp, hs,
        pre_app_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, relMapLift_snd, relMapRestrict_snd, Category.id_comp]
  refine ⟨g, ⟨by rw [hρg]; exact Homotopy.refl' _⟩, ⟨Homotopy.mk' H ?_ ?_⟩⟩
  · apply relMap_hom_ext
    · rw [Category.assoc, relMapLift_fst, ι₀_comp_assoc, ι₀_preHomotopy, hG₀, pre_app_comp,
        Category.assoc, relMapRestrict_fst, relMapLift_fst_assoc, Category.assoc]
    · rw [Category.assoc, relMapLift_snd, ι₀_fst_assoc, Category.assoc, relMapRestrict_snd,
        relMapLift_snd]
  · apply relMap_hom_ext
    · rw [Category.assoc, relMapLift_fst, ι₁_comp_assoc, ι₁_preHomotopy, hG₁, pre_app_id,
        Category.comp_id (relMapFst _ _), Category.id_comp]
    · rw [Category.assoc, relMapLift_snd, ι₁_fst_assoc, Category.id_comp]

/-! ### Composition with a right anodyne map -/

/-- The composite of a right anodyne map with a cofinal map is cofinal (the only composition
law Theorem A needs). By `relMapRestrict_comp`, restriction along `i ≫ q` is restriction along
`q` (a homotopy equivalence since `q` is cofinal) followed by restriction along `i` (a trivial
fibration); the relative mapping spaces are Kan complexes, so homotopy equivalences compose. -/
theorem isCofinal_comp_of_rightAnodyneExtensions {S Z C : SSet.{u}} {i : S ⟶ Z}
    (hi : rightAnodyneExtensions i) {q : Z ⟶ C} (hq : IsCofinal q) : IsCofinal (i ≫ q) := by
  intro X r _
  rw [relMapRestrict_comp]
  exact (hq X r).comp (isHomotopyEquivalence_relMapRestrict_of_rightAnodyneExtensions hi _ r)

end SSet
