/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Anodyne.UniversalColimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Closure properties of "base changes along `Q` lie in `P`"

For morphism properties `Q P` on `SSet.{u}`, `SSet.baseChangeAlong Q P` is the class of
morphisms `f : A ⟶ B` such that for every `u : U ⟶ B` in `Q`, the base change
`pullback.snd f u : pullback f u ⟶ U` lies in `P`. This is the class one saturates in the
proof that right anodyne extensions are stable under base change along left fibrations
([Lur09, 4.1.2.15], "left fibrations are smooth"): with `Q := leftFibrations` and
`P := rightAnodyneExtensions`, the small object argument for right horn inclusions reduces
the statement to the closure properties proved here.

The colimit-flavoured closure properties all follow the same pattern: pull the colimit
cocone back along `u`, use universality of colimits in `SSet` (`SSet.isUniversalColimit`)
to see that the pulled-back cocone is again a colimit, and identify the transition maps of
the pulled-back diagram with base changes of the original transition maps along morphisms
of `Q` (using that `Q` is stable under base change).

* `SSet.pullbackDiagram`, `SSet.pullbackCocone`, `SSet.pullbackDiagramHom` : the diagram,
  cocone and projection obtained by pulling back the legs of a cocone `c` along
  `u : U ⟶ c.pt`; `SSet.isColimitPullbackCocone` says the pulled-back cocone is a colimit
  whenever `c` is, and `SSet.equifibered_pullbackDiagramHom` records that the projection is
  equifibered, i.e. that transition maps pull back to transition maps.
* `SSet.pullbackDiagramMap` : the pullback of a morphism of cocones, with its pullback
  squares `SSet.isPullback_pullbackDiagramMap_app`.
* `SSet.iff_pullback_snd_of_isPullback` : when `P` respects isomorphisms, `P b ↔ P (pullback.snd
  f u)` for any pullback square `IsPullback a b f u`.
* `SSet.baseChangeAlong`, `SSet.baseChangeAlong_iff`, `SSet.baseChangeAlong_iff_isPullback`,
  `SSet.baseChangeAlong.of_isPullback` : the class and its characterisation by arbitrary
  pullback squares (when `P` respects isomorphisms); `SSet.baseChangeAlong.map_pullbackDiagram`
  puts the transition maps of a pulled-back diagram in `P`.
* Instances, for `Q` stable under base change and `P` respecting isomorphisms:
  `baseChangeAlong Q P` respects isomorphisms, is stable under retracts, cobase change,
  colimits of any shape `J` (`SSet.baseChangeAlong.isStableUnderColimitsOfShape`, in
  particular `u`-small coproducts) and transfinite compositions of shape `ℕ`, as soon as
  `P` has the corresponding property.
-/

universe w w' u

open CategoryTheory Limits MorphismProperty

-- The objects of `pullbackDiagram` are pullbacks only up to unfolding a definition; as in
-- Mathlib's own `pullback.map` lemmas, let `simp`/`rw` see through it.
set_option backward.isDefEq.respectTransparency false

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

noncomputable section

namespace SSet

section PullbackCocone

variable {J : Type w} [Category.{w'} J] {F : J ⥤ SSet.{u}} (c : Cocone F) {U : SSet.{u}}
  (u : U ⟶ c.pt)

/-- The diagram obtained by pulling back the legs of the cocone `c` along `u : U ⟶ c.pt`. -/
@[simps]
def pullbackDiagram : J ⥤ SSet.{u} where
  obj j := pullback (c.ι.app j) u
  map {i j} g := pullback.lift (pullback.fst (c.ι.app i) u ≫ F.map g) (pullback.snd (c.ι.app i) u)
    (by rw [Category.assoc, c.w g, pullback.condition])
  map_id j := by apply pullback.hom_ext <;> simp
  map_comp g h := by apply pullback.hom_ext <;> simp

/-- The pulled-back cocone: its point is `U` and its legs are the second projections. -/
@[simps]
def pullbackCocone : Cocone (pullbackDiagram c u) where
  pt := U
  ι :=
    { app := fun j ↦ pullback.snd (c.ι.app j) u
      naturality := fun i j g ↦ by simp }

/-- The projection from the pulled-back diagram to the original one. -/
@[simps]
def pullbackDiagramHom : pullbackDiagram c u ⟶ F where
  app j := pullback.fst (c.ι.app j) u
  naturality := fun i j g ↦ by simp

lemma isPullback_pullbackCocone (j : J) :
    IsPullback ((pullbackCocone c u).ι.app j) ((pullbackDiagramHom c u).app j) u
      (c.ι.app j) :=
  (IsPullback.of_hasPullback _ _).flip

/-- Transition maps of the pulled-back diagram are base changes of the original ones. -/
lemma equifibered_pullbackDiagramHom : NatTrans.Equifibered (pullbackDiagramHom c u) := by
  intro i j g
  refine IsPullback.of_right ?_ (by simp) (isPullback_pullbackCocone c u j)
  rw [(pullbackCocone c u).w g, c.w g]
  exact isPullback_pullbackCocone c u i

/-- The pulled-back cocone is a colimit, by universality of colimits in `SSet`. -/
def isColimitPullbackCocone [HasColimitsOfShape J (Type u)]
    (hc : IsColimit c) : IsColimit (pullbackCocone c u) :=
  (SSet.isUniversalColimit c hc (pullbackCocone c u) (pullbackDiagramHom c u) u
    (NatTrans.ext (funext fun _ ↦ pullback.condition))
    (equifibered_pullbackDiagramHom c u) (isPullback_pullbackCocone c u)).some

variable {c u}

/-- A morphism of cocones `(f, φ) : c₁ ⟶ c₂` pulls back along `u : U ⟶ c₂.pt` to a
morphism of the pulled-back diagrams (over `pullback.snd φ u : pullback φ u ⟶ U`). -/
@[simps]
def pullbackDiagramMap {X₁ X₂ : J ⥤ SSet.{u}} {c₁ : Cocone X₁} {c₂ : Cocone X₂} (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) (u : U ⟶ c₂.pt) :
    pullbackDiagram c₁ (pullback.fst φ u) ⟶ pullbackDiagram c₂ u where
  app j := pullback.lift (pullback.fst (c₁.ι.app j) (pullback.fst φ u) ≫ f.app j)
    (pullback.snd (c₁.ι.app j) (pullback.fst φ u) ≫ pullback.snd φ u)
    (by rw [Category.assoc, ← hφ j, pullback.condition_assoc, Category.assoc, pullback.condition])
  naturality _ _ _ := by apply pullback.hom_ext <;> simp

/-- The components of `pullbackDiagramMap` are base changes of the components of `f`. -/
lemma isPullback_pullbackDiagramMap_app {X₁ X₂ : J ⥤ SSet.{u}} {c₁ : Cocone X₁}
    {c₂ : Cocone X₂} (f : X₁ ⟶ X₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) (u : U ⟶ c₂.pt) (j : J) :
    IsPullback ((pullbackDiagramHom c₁ (pullback.fst φ u)).app j)
      ((pullbackDiagramMap f φ hφ u).app j) (f.app j) ((pullbackDiagramHom c₂ u).app j) := by
  refine (IsPullback.of_right ?_ (by simp) (isPullback_pullbackCocone c₂ u j)).flip
  have := (isPullback_pullbackCocone c₁ (pullback.fst φ u) j).paste_horiz
    (IsPullback.of_hasPullback φ u).flip
  rwa [show (pullbackDiagramMap f φ hφ u).app j ≫ (pullbackCocone c₂ u).ι.app j =
    (pullbackCocone c₁ (pullback.fst φ u)).ι.app j ≫ pullback.snd φ u by simp, ← hφ j]

end PullbackCocone

/-- `baseChangeAlong Q P f` : every base change of `f` along a morphism in `Q` lies in `P`. -/
def baseChangeAlong (Q P : MorphismProperty SSet.{u}) : MorphismProperty SSet.{u} :=
  fun _ B f ↦ ∀ ⦃U : SSet.{u}⦄ (u : U ⟶ B), Q u → P (pullback.snd f u)

variable (Q P : MorphismProperty SSet.{u})

lemma baseChangeAlong_iff {A B : SSet.{u}} (f : A ⟶ B) :
    baseChangeAlong Q P f ↔ ∀ ⦃U : SSet.{u}⦄ (u : U ⟶ B), Q u → P (pullback.snd f u) :=
  Iff.rfl

/-- When `P` respects isomorphisms, membership of a base change of `f` in `P` can be tested
on any pullback square. -/
lemma iff_pullback_snd_of_isPullback [P.RespectsIso] {X A B U : SSet.{u}} {a : X ⟶ A}
    {b : X ⟶ U} {f : A ⟶ B} {u : U ⟶ B} (sq : IsPullback a b f u) :
    P b ↔ P (pullback.snd f u) := by
  rw [← sq.isoPullback_hom_snd, P.cancel_left_of_respectsIso]

variable {Q P}

lemma baseChangeAlong.of_isPullback [P.RespectsIso] {A B X U : SSet.{u}} {f : A ⟶ B}
    (hf : baseChangeAlong Q P f) {u : U ⟶ B} (hu : Q u) {a : X ⟶ A} {b : X ⟶ U}
    (sq : IsPullback a b f u) : P b :=
  (iff_pullback_snd_of_isPullback P sq).2 (hf u hu)

variable (Q P) in
lemma baseChangeAlong_iff_isPullback [P.RespectsIso] {A B : SSet.{u}} (f : A ⟶ B) :
    baseChangeAlong Q P f ↔
      ∀ ⦃X U : SSet.{u}⦄ (a : X ⟶ A) (b : X ⟶ U) (u : U ⟶ B), IsPullback a b f u → Q u → P b :=
  ⟨fun hf _ _ _ _ _ sq hu ↦ hf.of_isPullback hu sq,
    fun h _ u hu ↦ h _ _ u (IsPullback.of_hasPullback f u) hu⟩

/-- Transition maps of a pulled-back diagram lie in `P` when the original transition maps
lie in `baseChangeAlong Q P` and `u` lies in `Q`. -/
lemma baseChangeAlong.map_pullbackDiagram [Q.IsStableUnderBaseChange] [P.RespectsIso]
    {J : Type w} [Category.{w'} J] {F : J ⥤ SSet.{u}} (c : Cocone F) {U : SSet.{u}}
    (u : U ⟶ c.pt) {i j : J} (g : i ⟶ j) (hg : baseChangeAlong Q P (F.map g)) (hu : Q u) :
    P ((pullbackDiagram c u).map g) :=
  hg.of_isPullback (Q.pullback_fst _ _ hu) (equifibered_pullbackDiagramHom c u g).flip

variable (Q P) [Q.IsStableUnderBaseChange] [P.RespectsIso]

instance : (baseChangeAlong Q P).RespectsIso := by
  refine RespectsIso.mk _ (fun e f hf ↦ ?_) (fun e f hf ↦ ?_)
  · intro U u hu
    exact hf.of_isPullback (a := pullback.fst (e.hom ≫ f) u ≫ e.hom) hu
      ((IsPullback.of_hasPullback (e.hom ≫ f) u).of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp))
  · intro U u hu
    exact hf.of_isPullback (a := pullback.fst (f ≫ e.hom) u) (RespectsIso.postcomp Q e.inv u hu)
      ((IsPullback.of_hasPullback (f ≫ e.hom) u).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
        e.symm (by simp) (by simp) (by simp) (by simp))

instance [P.IsStableUnderRetracts] : (baseChangeAlong Q P).IsStableUnderRetracts where
  of_retract {X Y Z W f g} h hg := by
    intro U u hu
    -- `v : U' ⟶ W` is the base change of `u` along the retraction `W ⟶ Y`; it lies in `Q`.
    have hv : Q (pullback.fst h.r.right u) := Q.pullback_fst _ _ hu
    -- `U ⟶ U'` splits the projection `U' ⟶ U`.
    let ι : U ⟶ pullback h.r.right u := pullback.lift (u ≫ h.i.right) (𝟙 U) (by simp)
    refine of_retract ?_ (hg _ hv)
    exact
      { i := Arrow.homMk' (pullback.lift (pullback.fst f u ≫ h.i.left) (pullback.snd f u ≫ ι)
            (by simp [ι, h.i_w, pullback.condition_assoc])) ι (by simp)
        r := Arrow.homMk' (pullback.lift (pullback.fst g _ ≫ h.r.left)
            (pullback.snd g _ ≫ pullback.snd h.r.right u)
            (by simp [h.r_w, pullback.condition_assoc, pullback.condition]))
            (pullback.snd h.r.right u) (by simp)
        retract := Arrow.hom_ext _ _
          (pullback.hom_ext (by simp) (by simp [ι])) (by simp [ι]) }

instance [P.IsStableUnderCobaseChange] : (baseChangeAlong Q P).IsStableUnderCobaseChange where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    intro U u hu
    exact IsStableUnderCobaseChange.of_isPushout
      (IsPushout.of_isColimit_cocone (isColimitPullbackCocone sq.cocone u sq.isColimit))
      (baseChangeAlong.map_pullbackDiagram sq.cocone u WalkingSpan.Hom.snd hf hu)

/-- `baseChangeAlong Q P` is stable under colimits of any shape `J` under which `P` is
stable (and for which `Type u` has colimits). -/
lemma baseChangeAlong.isStableUnderColimitsOfShape (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J (Type u)] [P.IsStableUnderColimitsOfShape J] :
    (baseChangeAlong Q P).IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    intro U u hu
    exact IsStableUnderColimitsOfShape.condition _ _ _ _
      (isColimitPullbackCocone c₁ (pullback.fst φ u) h₁) (isColimitPullbackCocone c₂ u h₂)
      (pullbackDiagramMap f φ hφ u)
      (fun j ↦ (hf j).of_isPullback (Q.pullback_fst _ _ hu)
        (isPullback_pullbackDiagramMap_app f φ hφ u j))
      (pullback.snd φ u) (fun j ↦ by simp)

instance [IsStableUnderCoproducts.{u} P] : IsStableUnderCoproducts.{u} (baseChangeAlong Q P) where
  isStableUnderCoproductsOfShape _ := baseChangeAlong.isStableUnderColimitsOfShape Q P _

instance [P.IsStableUnderTransfiniteCompositionOfShape ℕ] :
    (baseChangeAlong Q P).IsStableUnderTransfiniteCompositionOfShape ℕ where
  le := by
    rintro X Y f ⟨h⟩ U u hu
    let c : Cocone h.F := Cocone.mk Y h.incl
    let h' : P.TransfiniteCompositionOfShape ℕ (pullback.snd (h.incl.app ⊥) u) :=
      { F := pullbackDiagram c u
        isoBot := Iso.refl _
        incl := (pullbackCocone c u).ι
        isColimit := isColimitPullbackCocone c u h.isColimit
        map_mem := fun n hn ↦ baseChangeAlong.map_pullbackDiagram c u _ (h.map_mem n hn) hu }
    have sq : IsPullback (pullback.fst (h.incl.app ⊥) u ≫ h.isoBot.hom)
        (pullback.snd (h.incl.app ⊥) u) f u :=
      (IsPullback.of_hasPullback _ _).of_iso (Iso.refl _) h.isoBot (Iso.refl _) (Iso.refl _)
        (by simp) (by simp)
        (by simpa using (Iso.inv_comp_eq _).1 h.fac) (by simp)
    exact (iff_pullback_snd_of_isPullback P sq).1
      (P.transfiniteCompositionsOfShape_le ℕ _ (TransfiniteCompositionOfShape.mem _ h'))

end SSet

end
