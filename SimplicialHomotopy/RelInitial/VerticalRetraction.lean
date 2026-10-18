/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.RelInitial.PrismCone
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# A vertical deformation retraction onto a subcomplex of relatively initial vertices

Let `p : X ⟶ Y` be any map of simplicial sets and `Xn ⊆ X` a full subcomplex (a simplex lies in
`Xn` once all its vertices do). Suppose every vertex `y` of `Xn` satisfies
`∀ B₀, HasConeLiftAt p y B₀`, and every vertex of `X` has the same `p`-image as some vertex of `Xn`.
Then `SSet.exists_verticalRetraction` gives a homotopy `h : X ⊗ Δ[1] ⟶ X` that is the identity at
time `1`, lies over `Y` (`h ≫ p = fst ≫ p`), and lands in `Xn` at time `0`.

Proof: `SSet.vertRetr.PSub p Xn` is the subcomplex of the pullback of `(ihom Δ[1]).map p` along
the constant paths of `Y` made of paths starting in `Xn`, and `SSet.vertRetr.π` evaluates at `1`.
`SSet.vertRetr.hasLiftingProperty_boundary_π` shows `π` lifts against every `∂Δ[n].ι`; the prism
lifting problem is solved by `SSet.vertRetr.exists_prism_lift` via
`SSet.prism.exists_lift_of_preimage`. So `π` has the right lifting property against all
monomorphisms (`SSet.rlp_monomorphisms`), hence a section, whose adjoint is `h`.
-/

universe u
open CategoryTheory Simplicial MonoidalCategory Opposite

namespace SSet

namespace vertRetr

open MonoidalClosed Limits CartesianMonoidalCategory

variable {X Y W : SSet.{u}}

/-- The vertex `i` of `Δ[1]`. -/
abbrev vt (i : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌ := stdSimplex.obj₀Equiv.symm i

/-- The constant paths `Y ⟶ Fun(Δ[1], Y)`. -/
noncomputable def constPath (Y : SSet.{u}) : Y ⟶ (ihom Δ[1]).obj Y := curry (snd _ _)

/-- Evaluation `Fun(Δ[1], X) ⟶ X` at the vertex `i`. -/
noncomputable def evAt (i : Fin 2) (X : SSet.{u}) : (ihom Δ[1]).obj X ⟶ X :=
  lift (const (vt i)) (𝟙 _) ≫ (ihom.ev Δ[1]).app X

lemma comp_evAt (i : Fin 2) (g : W ⟶ (ihom Δ[1]).obj X) :
    g ≫ evAt i X = lift (const (vt i)) (𝟙 W) ≫ uncurry g := by
  rw [uncurry_eq, evAt, ← Category.assoc, ← Category.assoc]
  congr 1

lemma curry_comp_evAt (i : Fin 2) (l : Δ[1] ⊗ W ⟶ X) :
    curry l ≫ evAt i X = lift (const (vt i)) (𝟙 W) ≫ l := by
  rw [comp_evAt, uncurry_curry]

variable (p : X ⟶ Y) (Xn : X.Subcomplex)

/-- The paths whose image under `p` is constant, with the constant value recorded. -/
noncomputable abbrev P₁ : SSet.{u} := pullback ((ihom Δ[1]).map p) (constPath Y)

/-- The path object: paths `h` in `X` with `p ∘ h` constant and `h 0 ∈ Xn`. -/
noncomputable abbrev PSub : (P₁ p).Subcomplex :=
  Xn.preimage (pullback.fst _ _ ≫ evAt 0 X)

/-- Evaluation at `1`, `PSub p Xn ⟶ X`. -/
noncomputable def π : (PSub p Xn : SSet.{u}) ⟶ X :=
  (PSub p Xn).ι ≫ pullback.fst _ _ ≫ evAt 1 X

variable {p Xn}

/-- A map into the path object from a homotopy. -/
noncomputable def mk (l : Δ[1] ⊗ W ⟶ X) (b : W ⟶ Y) (hl : l ≫ p = snd _ _ ≫ b)
    (h₀ : Subcomplex.range (lift (const (vt 0)) (𝟙 W) ≫ l) ≤ Xn) :
    W ⟶ (PSub p Xn : SSet.{u}) :=
  Subcomplex.lift (pullback.lift (curry l) b (by
      rw [← curry_natural_right, hl, constPath, ← curry_natural_left, whiskerLeft_snd]))
    (by
      rw [← Subcomplex.image_le_iff, ← Subcomplex.range_comp,
        pullback.lift_fst_assoc, curry_comp_evAt]
      exact h₀)

@[reassoc (attr := simp)]
lemma mk_ι_fst (l : Δ[1] ⊗ W ⟶ X) (b : W ⟶ Y) (hl) (h₀) :
    mk (p := p) (Xn := Xn) l b hl h₀ ≫ (PSub p Xn).ι ≫ pullback.fst _ _ = curry l := by
  rw [mk, Subcomplex.lift_ι_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma mk_ι_snd (l : Δ[1] ⊗ W ⟶ X) (b : W ⟶ Y) (hl) (h₀) :
    mk (p := p) (Xn := Xn) l b hl h₀ ≫ (PSub p Xn).ι ≫ pullback.snd _ _ = b := by
  rw [mk, Subcomplex.lift_ι_assoc, pullback.lift_snd]

lemma mk_π (l : Δ[1] ⊗ W ⟶ X) (b : W ⟶ Y) (hl) (h₀) :
    mk (p := p) (Xn := Xn) l b hl h₀ ≫ π p Xn = lift (const (vt 1)) (𝟙 W) ≫ l := by
  rw [π, mk_ι_fst_assoc, curry_comp_evAt]

lemma hom_ext {f g : W ⟶ (PSub p Xn : SSet.{u})}
    (h₁ : f ≫ (PSub p Xn).ι ≫ pullback.fst _ _ = g ≫ (PSub p Xn).ι ≫ pullback.fst _ _)
    (h₂ : f ≫ (PSub p Xn).ι ≫ pullback.snd _ _ = g ≫ (PSub p Xn).ι ≫ pullback.snd _ _) :
    f = g := by
  rw [← cancel_mono (PSub p Xn).ι]
  exact pullback.hom_ext (by simpa using h₁) (by simpa using h₂)

/-- The homotopy underlying a map into the path object. -/
noncomputable def homotopy (t : W ⟶ (PSub p Xn : SSet.{u})) : Δ[1] ⊗ W ⟶ X :=
  uncurry (t ≫ (PSub p Xn).ι ≫ pullback.fst _ _)

lemma homotopy_comp (t : W ⟶ (PSub p Xn : SSet.{u})) :
    homotopy t ≫ p = snd _ _ ≫ t ≫ (PSub p Xn).ι ≫ pullback.snd _ _ := by
  rw [homotopy, ← uncurry_natural_right, Category.assoc, Category.assoc, pullback.condition]
  have : uncurry (constPath Y) = snd _ _ := uncurry_curry _
  rw [← Category.assoc, ← Category.assoc, uncurry_natural_left, this, whiskerLeft_snd,
    Category.assoc]

lemma range_homotopy_zero (t : W ⟶ (PSub p Xn : SSet.{u})) :
    Subcomplex.range (lift (const (vt 0)) (𝟙 W) ≫ homotopy t) ≤ Xn := by
  rw [homotopy, ← comp_evAt, Category.assoc, Subcomplex.range_comp]
  refine (Subcomplex.image_le_iff _ _ _).2 ?_
  rintro _ _ ⟨x, rfl⟩
  exact (t.app _ x).2

lemma lift_homotopy_one (t : W ⟶ (PSub p Xn : SSet.{u})) :
    lift (const (vt 1)) (𝟙 W) ≫ homotopy t = t ≫ π p Xn := by
  rw [homotopy, ← comp_evAt, π]
  simp only [Category.assoc]

lemma face_one_ι : (stdSimplex.face.{u} ({1} : Finset (Fin 2))).ι = const (vt 1) := by
  refine NatTrans.ext (funext fun ⟨⟨m⟩⟩ ↦ ConcreteCategory.hom_ext _ _ fun ⟨z, hz⟩ ↦ ?_)
  refine stdSimplex.objEquiv.injective (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _
    (funext fun k ↦ ?_)))
  have hk := ((stdSimplex.mem_face_iff _ _).1 hz) k
  rw [Finset.mem_singleton] at hk
  exact hk

lemma whiskerRight_face_one (T : SSet.{u}) :
    (stdSimplex.face.{u} ({1} : Finset (Fin 2))).ι ▷ T = snd _ _ ≫ lift (const (vt 1)) (𝟙 T) := by
  ext : 1
  · rw [whiskerRight_fst, face_one_ι, comp_const, Category.assoc, lift_fst, comp_const]
  · rw [whiskerRight_snd, Category.assoc, lift_snd, Category.comp_id]

lemma const_yonedaEquiv (s : Δ[0] ⟶ X) : const (yonedaEquiv s) = s :=
  yonedaEquiv.injective (yonedaEquiv_const _)

variable (Xn) in
/-- A full subcomplex contains a simplex as soon as it contains its vertices. -/
lemma range_le_of_vertices
    (hfull : ∀ (n : ℕ) (σ : X _⦋n⦌),
      (∀ i : Fin (n + 1), X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ ∈ Xn.obj (op ⦋0⦌)) →
        σ ∈ Xn.obj (op ⦋n⦌))
    {n : ℕ} (f : Δ[n] ⟶ X)
    (h : ∀ i : Fin (n + 1),
      Subcomplex.range (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) ≫ f) ≤ Xn) :
    Subcomplex.range f ≤ Xn := by
  rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
  refine hfull n _ fun i ↦ ?_
  have := h i
  rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff] at this
  rwa [yonedaEquiv_naturality]

open prism in
/-- The prism lifting problem in the proof of `hasLiftingProperty_boundary_π`: given the
homotopy `g` on `Δ[1] ⊗ ∂Δ[n]` (starting in `Xn`) and `s` on `{1} ⊗ Δ[n]`, glued to `aK` on
`K n`, a lift over `snd ≫ s ≫ p` starting in `Xn`. -/
lemma exists_prism_lift
    (hfull : ∀ (n : ℕ) (σ : X _⦋n⦌),
      (∀ i : Fin (n + 1), X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ ∈ Xn.obj (op ⦋0⦌)) →
        σ ∈ Xn.obj (op ⦋n⦌))
    (hinit : ∀ y ∈ Xn.obj (op ⦋0⦌), ∀ {B : SSet.{u}} (B₀ : B.Subcomplex), HasConeLiftAt p y B₀)
    (hsurj : ∀ x : X _⦋0⦌, ∃ y ∈ Xn.obj (op ⦋0⦌), p.app _ y = p.app _ x) (n : ℕ)
    (g : Δ[1] ⊗ (boundary n : SSet.{u}) ⟶ X) (s : Δ[n] ⟶ X) (aK : (K.{u} n : SSet.{u}) ⟶ X)
    (haK₁ : Subcomplex.unionProd.ι₁ _ _ ≫ aK = g)
    (F3 : Subcomplex.range (lift (const (vt 0)) (𝟙 _) ≫ g) ≤ Xn)
    (sqK : aK ≫ p = (K n).ι ≫ snd _ _ ≫ s ≫ p) :
    ∃ l : Δ[1] ⊗ Δ[n] ⟶ X, (K n).ι ≫ l = aK ∧ l ≫ p = snd _ _ ≫ s ≫ p ∧
      Subcomplex.range (lift (const (vt 0)) (𝟙 _) ≫ l) ≤ Xn := by
  have hconst : ∀ y : X _⦋0⦌, Subcomplex.range (const y : Δ[0] ⟶ X) ≤ Xn ↔ y ∈ Xn.obj _ :=
    fun y ↦ by rw [Subcomplex.range_eq_ofSimplex, yonedaEquiv_const, Subcomplex.ofSimplex_le_iff]
  cases n with
  | zero =>
    have hdisj : ∀ (m : SimplexCategoryᵒᵖ) (z : (Δ[1] ⊗ Δ[0] : SSet.{u}).obj m),
        z ∈ (K 0).obj m → z ∈ (V 0).obj m → False := by
      rintro ⟨⟨m⟩⟩ z hK ⟨hV₁, -⟩
      rcases (Subcomplex.mem_unionProd_iff _ _ z).1 hK with hb | h1
      · obtain ⟨j, hj⟩ := (mem_boundary_iff_notMem_range z.2).1 hb
        exact hj ⟨0, Fin.ext (by have := j.isLt; have := (z.2 0).isLt; omega)⟩
      · have a := (stdSimplex.mem_face_iff _ _).1 h1 0
        have b := (stdSimplex.mem_face_iff _ _).1 hV₁ 0
        rw [Finset.mem_singleton] at a b
        exact absurd (a.symm.trans b) (by decide)
    have sq0 : Subcomplex.BicartSq (K.{u} 0 ⊓ V 0) (K 0) (V 0) (K 0 ⊔ V 0) := ⟨rfl, rfl⟩
    obtain ⟨y, hy, hpy⟩ := hsurj (yonedaEquiv s)
    let aZ : ((K.{u} 0 ⊔ V 0 : Subcomplex _) : SSet.{u}) ⟶ X :=
      sq0.isPushout.desc aK (const y) (by
        ext _ ⟨z, hzK, hzV⟩
        exact (hdisj _ z hzK hzV).elim)
    have haZ₁ : Subcomplex.homOfLE sq0.le₂₄ ≫ aZ = aK := sq0.isPushout.inl_desc _ _ _
    have haZ₂ : Subcomplex.homOfLE sq0.le₃₄ ≫ aZ = const y := sq0.isPushout.inr_desc _ _ _
    have sqZ : aZ ≫ p = (K 0 ⊔ V 0).ι ≫ snd _ _ ≫ s ≫ p := by
      apply sq0.isPushout.hom_ext
      · rw [← Category.assoc, haZ₁, sqK, ← Subcomplex.homOfLE_ι sq0.le₂₄, Category.assoc]
      · rw [← Category.assoc, haZ₂, ← Category.assoc (Subcomplex.homOfLE sq0.le₃₄),
          Subcomplex.homOfLE_ι, ← const_yonedaEquiv s, const_comp, ← Category.assoc,
          ← Category.assoc, comp_const, const_comp, hpy]
    have h₀₀ : v₀₀.{u} 0 ∈ (K 0 ⊔ V 0).obj _ := Or.inr (v₀₀_mem_V 0)
    have hv : aZ.app _ ⟨v₀₀ 0, h₀₀⟩ = y := by
      have := congrArg (fun f ↦ f.app (op ⦋0⦌) ⟨v₀₀ 0, v₀₀_mem_V 0⟩) haZ₂
      exact this.trans (const_app_zero_apply _ _)
    obtain ⟨l, hl₁, hl₂⟩ := exists_lift_of_preimage p y 0 (hinit y hy _) (K 0 ⊔ V 0)
      (preimage_KV 0) h₀₀ aZ _ sqZ hv
    refine ⟨l, ?_, hl₂, ?_⟩
    · rw [← Subcomplex.homOfLE_ι sq0.le₂₄, Category.assoc, hl₁, haZ₁]
    · have : lift (const (vt 0)) (𝟙 Δ[0]) =
          const (⟨v₀₀ 0, h₀₀⟩ : ((K.{u} 0 ⊔ V 0 : Subcomplex _) : SSet.{u}) _⦋0⦌) ≫
            (K 0 ⊔ V 0).ι := by
        ext : 1
        · rw [lift_fst, Category.assoc, const_comp]
          rfl
        · exact stdSimplex.ext₀
      rw [this, Category.assoc, hl₁, const_comp, hv, hconst]
      exact hy
  | succ n =>
    have hvert : ∀ i : Fin (n + 2), Subcomplex.range
        (stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ i)) ≤ boundary.{u} (n + 1) := by
      intro i
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff, yonedaEquiv_map,
        mem_boundary_iff_notMem_range]
      refine ⟨if i = 0 then 1 else 0, ?_⟩
      rintro ⟨k, hk⟩
      change i = _ at hk
      split_ifs at hk with h
      · exact absurd (hk.symm.trans h) (by simp)
      · exact h hk
    have hVK : V.{u} (n + 1) ≤ K (n + 1) := by
      intro _ z hz
      refine (Subcomplex.mem_unionProd_iff _ _ z).2 (Or.inl ?_)
      rw [mem_boundary_iff_notMem_range]
      refine ⟨1, ?_⟩
      rintro ⟨k, hk⟩
      have := (stdSimplex.mem_face_iff _ _).1 hz.2 k
      rw [Finset.mem_singleton, hk] at this
      exact absurd this (by simp)
    have hZ : (K.{u} (n + 1)).preimage (coneIso (n + 1)).hom = coneUnion (B₀ (n + 1)) := by
      rw [← sup_eq_left.2 hVK]
      exact preimage_KV _
    have h₀₀ : v₀₀.{u} (n + 1) ∈ (K (n + 1)).obj _ := hVK _ (v₀₀_mem_V _)
    have hι : ∀ l : Δ[1] ⊗ Δ[n + 1] ⟶ X, (K (n + 1)).ι ≫ l = aK →
        (boundary (n + 1)).ι ≫ lift (const (vt 0)) (𝟙 _) ≫ l = lift (const (vt 0)) (𝟙 _) ≫ g := by
      intro l hl
      rw [← haK₁, ← hl, Subcomplex.unionProd.ι₁_ι_assoc, lift_whiskerLeft_assoc, ← Category.assoc,
        comp_lift, comp_const, Category.comp_id, Category.id_comp]
    have hd : (stdSimplex.obj₀Equiv.symm 0 : Δ[n + 1] _⦋0⦌) ∈ (boundary (n + 1)).obj _ := by
      have := hvert 0
      rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff, yonedaEquiv_map] at this
      exact this
    have e : (const (⟨v₀₀ (n + 1), h₀₀⟩ : (K.{u} (n + 1) : SSet.{u}) _⦋0⦌) : Δ[0] ⟶ _) =
        (const (⟨_, hd⟩ : (boundary.{u} (n + 1) : SSet.{u}) _⦋0⦌) : Δ[0] ⟶ _) ≫
          lift (const (vt 0)) (𝟙 _) ≫ Subcomplex.unionProd.ι₁ _ _ := by
      rw [← cancel_mono (K (n + 1)).ι, Category.assoc, Category.assoc,
        Subcomplex.unionProd.ι₁_ι, lift_whiskerLeft, comp_lift, comp_const, Category.id_comp]
      ext : 1
      · rw [lift_fst, const_comp, const_comp]
        rfl
      · rw [lift_snd, const_comp, const_comp, const_comp]
        rfl
    have hy : aK.app _ ⟨v₀₀ (n + 1), h₀₀⟩ ∈ Xn.obj _ := by
      rw [← hconst, ← const_comp, e, Category.assoc, Category.assoc, haK₁]
      exact (Subfunctor.range_comp_le _ _).trans F3
    obtain ⟨l, hl₁, hl₂⟩ := exists_lift_of_preimage p _ (n + 1) (hinit _ hy _) (K (n + 1))
      hZ h₀₀ aK _ sqK rfl
    refine ⟨l, hl₁, hl₂, range_le_of_vertices Xn hfull _ fun i ↦ ?_⟩
    rw [← Subcomplex.lift_ι _ (hvert i), Category.assoc, hι l hl₁]
    exact (Subfunctor.range_comp_le _ _).trans F3

open prism in
/-- The evaluation `π p Xn : PSub p Xn ⟶ X` at the vertex `1` has the right lifting property
against every boundary inclusion `∂Δ[n] ↪ Δ[n]`: transposed, the lifting problem is the prism
problem solved by `exists_prism_lift`. -/
lemma hasLiftingProperty_boundary_π
    (hfull : ∀ (n : ℕ) (σ : X _⦋n⦌),
      (∀ i : Fin (n + 1), X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ ∈ Xn.obj (op ⦋0⦌)) →
        σ ∈ Xn.obj (op ⦋n⦌))
    (hinit : ∀ y ∈ Xn.obj (op ⦋0⦌), ∀ {B : SSet.{u}} (B₀ : B.Subcomplex), HasConeLiftAt p y B₀)
    (hsurj : ∀ x : X _⦋0⦌, ∃ y ∈ Xn.obj (op ⦋0⦌), p.app _ y = p.app _ x) (n : ℕ) :
    HasLiftingProperty (boundary.{u} n).ι (π p Xn) := by
  constructor
  intro t s sq
  let g := homotopy t
  let b₀ := t ≫ (PSub p Xn).ι ≫ pullback.snd _ _
  have F1 : g ≫ p = snd _ _ ≫ b₀ := homotopy_comp t
  have F2 : lift (const (vt 1)) (𝟙 _) ≫ g = (boundary n).ι ≫ s := by
    rw [lift_homotopy_one, sq.w]
  have F3 := range_homotopy_zero t
  have hb₀ : b₀ = (boundary n).ι ≫ s ≫ p := by
    have : lift (const (vt 1)) (𝟙 _) ≫ g ≫ p = b₀ := by
      rw [F1, lift_snd_assoc, Category.id_comp]
    rw [← this, ← Category.assoc, F2, Category.assoc]
  let S := stdSimplex.face.{u} ({1} : Finset (Fin 2))
  have w : S.ι ▷ _ ≫ g = (S : SSet.{u}) ◁ (boundary n).ι ≫ snd _ _ ≫ s := by
    rw [whiskerRight_face_one, Category.assoc, F2, whiskerLeft_snd_assoc]
  have hpo := Subcomplex.unionProd.isPushout S (boundary n)
  let aK : (K n : SSet.{u}) ⟶ X := hpo.desc g (snd _ _ ≫ s) w
  have haK₁ : Subcomplex.unionProd.ι₁ S (boundary n) ≫ aK = g := hpo.inl_desc _ _ _
  have haK₂ : Subcomplex.unionProd.ι₂ S (boundary n) ≫ aK = snd _ _ ≫ s := hpo.inr_desc _ _ _
  let b := snd Δ[1] Δ[n] ≫ s ≫ p
  have sqK : aK ≫ p = (K n).ι ≫ b := by
    apply hpo.hom_ext
    · rw [← Category.assoc, haK₁, F1, hb₀, Subcomplex.unionProd.ι₁_ι_assoc, whiskerLeft_snd_assoc]
    · rw [← Category.assoc, haK₂, Subcomplex.unionProd.ι₂_ι_assoc, whiskerRight_snd_assoc,
        Category.assoc]
  obtain ⟨l, hl₁, hl₂, hl₃⟩ : ∃ l : Δ[1] ⊗ Δ[n] ⟶ X, (K n).ι ≫ l = aK ∧ l ≫ p = b ∧
      Subcomplex.range (lift (const (vt 0)) (𝟙 _) ≫ l) ≤ Xn :=
    exists_prism_lift hfull hinit hsurj n g s aK haK₁ F3 sqK
  refine ⟨⟨{ l := mk l (s ≫ p) hl₂ hl₃, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply hom_ext
    · rw [Category.assoc, mk_ι_fst, ← curry_natural_left, ← Subcomplex.unionProd.ι₁_ι,
        Category.assoc, hl₁, haK₁]
      exact curry_uncurry _
    · rw [Category.assoc, mk_ι_snd]
      exact hb₀.symm
  · rw [mk_π]
    have : lift (const (vt 1)) (𝟙 Δ[n]) =
        lift (const (⟨vt 1, (stdSimplex.mem_face_iff _ _).2
          fun _ ↦ Finset.mem_singleton_self _⟩ : (S : SSet.{u}) _⦋0⦌)) (𝟙 _) ≫ S.ι ▷ Δ[n] := by
      rw [lift_whiskerRight, const_comp]
      rfl
    rw [this, Category.assoc, ← Subcomplex.unionProd.ι₂_ι, Category.assoc, hl₁, haK₂,
      lift_snd_assoc, Category.id_comp]

end vertRetr


section

open vertRetr MonoidalClosed Limits CartesianMonoidalCategory modelCategoryQuillen

/-- **Vertical deformation retraction.** If `Xn` is a full subcomplex of `X` whose vertices are
all `p`-initial in the strong sense `∀ B₀, HasConeLiftAt p y B₀`, and which meets every fibre of
`p` over a vertex of `X`, then `X` deforms over `Y` into `Xn`: there is `h : X ⊗ Δ[1] ⟶ X`, the
identity at `1`, with `h ≫ p = fst ≫ p`, and with image in `Xn` at `0`. -/
theorem exists_verticalRetraction {X Y : SSet.{u}} (p : X ⟶ Y) (Xn : X.Subcomplex)
    (hfull : ∀ (n : ℕ) (σ : X _⦋n⦌),
      (∀ i : Fin (n + 1), X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op σ ∈ Xn.obj (op ⦋0⦌)) →
        σ ∈ Xn.obj (op ⦋n⦌))
    (hinit : ∀ y ∈ Xn.obj (op ⦋0⦌), ∀ {B : SSet.{u}} (B₀ : B.Subcomplex), HasConeLiftAt p y B₀)
    (hsurj : ∀ x : X _⦋0⦌, ∃ y ∈ Xn.obj (op ⦋0⦌), p.app _ y = p.app _ x) :
    ∃ h : X ⊗ Δ[1] ⟶ X, ι₁ ≫ h = 𝟙 X ∧ h ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ p ∧
      Subcomplex.range (ι₀ ≫ h) ≤ Xn := by
  have hrlp : (MorphismProperty.monomorphisms SSet.{u}).rlp (π p Xn) := by
    rw [rlp_monomorphisms]
    rintro _ _ _ ⟨n⟩
    exact hasLiftingProperty_boundary_π hfull hinit hsurj n
  have sq : CommSq (Subcomplex.isInitialBot.to _) (⊥ : X.Subcomplex).ι (π p Xn) (𝟙 X) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  have := hrlp _ (inferInstance : Mono (⊥ : X.Subcomplex).ι)
  let sec := sq.lift
  have hsec : sec ≫ π p Xn = 𝟙 X := sq.fac_right
  have h₀ : (ι₀ : X ⟶ X ⊗ Δ[1]) ≫ (β_ Δ[1] X).inv = lift (const (vt 0)) (𝟙 X) := by
    ext1 <;> simp [ι₀]
  have h₁ : (ι₁ : X ⟶ X ⊗ Δ[1]) ≫ (β_ Δ[1] X).inv = lift (const (vt 1)) (𝟙 X) := by
    ext1 <;> simp [ι₁]
  refine ⟨(β_ Δ[1] X).inv ≫ homotopy sec, ?_, ?_, ?_⟩
  · rw [← Category.assoc, h₁, lift_homotopy_one, hsec]
  · have hb : sec ≫ (PSub p Xn).ι ≫ pullback.snd _ _ = p := by
      have := lift (const (vt 1)) (𝟙 X) ≫= homotopy_comp sec
      rw [lift_snd_assoc, Category.id_comp, ← Category.assoc, lift_homotopy_one,
        hsec, Category.id_comp] at this
      exact this.symm
    rw [Category.assoc, homotopy_comp, hb, ← Category.assoc]
    congr 1
  · rw [← Category.assoc, h₀]
    exact range_homotopy_zero sec

end
end SSet
