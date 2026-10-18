/-
Copyright (c) 2026 Yun Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yun Liu
-/
import SimplicialHomotopy.Cofinal.CofinalBasic
import SimplicialHomotopy.Fibration.Fiber
import SimplicialHomotopy.Equivalence.WeakEquivalenceKan

/-!
# Cofinal maps: the converse direction of Theorem A

The two facts that turn "`p` is cofinal" into "the fibres of the right-fibration replacement
of `p` are weakly contractible" ([Lur09, 4.1.3.1], converse direction):

* `SSet.isCofinal_of_comp_of_rightAnodyneExtensions`: if `i ≫ q` is cofinal and `i` is right
  anodyne then `q` is cofinal (2-out-of-3 on the relative mapping spaces, which are Kan
  complexes when the test map is a right fibration, `SSet.instKanComplexRelMap`);
* `SSet.weaklyContractible_fiber_of_isCofinal`: a cofinal right fibration `q : Z ⟶ C` has
  weakly contractible fibres. A homotopy inverse `g` of `Map_C(C, Z) ⟶ Map_C(Z, Z)` sends the
  vertex `𝟙 Z` to a section `s` of `q`, and the homotopy `g ≫ ρ ≃ 𝟙` evaluated at `𝟙 Z` is a
  fibrewise homotopy `G` from `q ≫ s` to `𝟙 Z`. Restricted to a fibre `Z_c`, `G` is a
  homotopy from an endomorphism `Φ` (which is constant, with value `s(c)`) to the identity,
  so `Z_c` is weakly contractible by `SSet.weaklyContractible_of_homotopy_id_const`.

The bookkeeping is organised around vertices and edges of `Map_B(A, X)`: a vertex
`𝟙_ SSet ⟶ Map_B(A, X)` is the same as a map `A ⟶ X` over `B` (`SSet.relMapVertex`,
`SSet.relMapHom`), and an edge `𝟙_ SSet ⊗ Δ[1] ⟶ Map_B(A, X)` gives a homotopy
`A ⊗ Δ[1] ⟶ X` over `B` (`SSet.relMapHomotopy`), whose ends are the maps classified by the
ends of the edge.
-/

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits CartesianMonoidalCategory

open scoped Simplicial

namespace SSet

/-! ### Cofinality descends along a right anodyne map -/

/-- Cofinality descends along a right anodyne map: if `i ≫ q` is cofinal and `i` is right
anodyne, then `q` is cofinal (2-out-of-3 on the relative mapping spaces, which are Kan). -/
theorem isCofinal_of_comp_of_rightAnodyneExtensions {S Z C : SSet.{u}} {i : S ⟶ Z}
    (hi : rightAnodyneExtensions i) (q : Z ⟶ C) (hp : IsCofinal (i ≫ q)) : IsCofinal q := by
  intro X r _
  have h := hp X r
  rw [relMapRestrict_comp] at h
  exact IsHomotopyEquivalence.of_comp_right h
    (isHomotopyEquivalence_relMapRestrict_of_rightAnodyneExtensions hi (q ≫ 𝟙 C) r)

/-! ### Vertices and edges of relative mapping spaces -/

section Vertices

variable {A B X : SSet.{u}} (f : A ⟶ B) (r : X ⟶ B)

/-- The vertex of `Map_B(A, X)` classifying a map `φ : A ⟶ X` over `B`. -/
noncomputable def relMapVertex (φ : A ⟶ X) (hφ : φ ≫ r = f) : 𝟙_ SSet.{u} ⟶ relMap f r :=
  relMapLift f r (pointOf φ) (𝟙 _)
    (by rw [pointOf, pointOf, ← curry_natural_right, Category.id_comp, Category.assoc, hφ])

/-- The map `A ⟶ X` classified by a vertex of `Map_B(A, X)`. -/
noncomputable def relMapHom (w : 𝟙_ SSet.{u} ⟶ relMap f r) : A ⟶ X :=
  (ρ_ A).inv ≫ uncurry (w ≫ relMapFst f r)

/-- The map classified by a vertex of `Map_B(A, X)` lies over `B`. -/
lemma relMapHom_comp (w : 𝟙_ SSet.{u} ⟶ relMap f r) : relMapHom f r w ≫ r = f := by
  have h : w ≫ relMapSnd f r = 𝟙 _ := toUnit_unique _ _
  rw [relMapHom, Category.assoc, ← uncurry_natural_right, Category.assoc, relMapFst_map,
    ← Category.assoc, h, Category.id_comp, pointOf, uncurry_curry, Iso.inv_hom_id_assoc]

lemma relMapHom_relMapVertex (φ : A ⟶ X) (hφ : φ ≫ r = f) :
    relMapHom f r (relMapVertex f r φ hφ) = φ := by
  rw [relMapHom, relMapVertex, relMapLift_fst, pointOf, uncurry_curry, Iso.inv_hom_id_assoc]

/-- Restriction along `p` acts on the classified maps by precomposition with `p`. -/
lemma relMapHom_comp_relMapRestrict {A' : SSet.{u}} (p : A' ⟶ A)
    (w : 𝟙_ SSet.{u} ⟶ relMap f r) :
    relMapHom (p ≫ f) r (w ≫ relMapRestrict p f r) = p ≫ relMapHom f r w := by
  rw [relMapHom, relMapHom, Category.assoc, relMapRestrict_fst, ← Category.assoc,
    uncurry_pre_app, rightUnitor_inv_naturality_assoc]

/-- The vertex `0` of `Δ[1]`, as a map from the unit. -/
def pt₀ : 𝟙_ SSet.{u} ⟶ Δ[1] := const (stdSimplex.obj₀Equiv.symm 0)

/-- The vertex `1` of `Δ[1]`, as a map from the unit. -/
def pt₁ : 𝟙_ SSet.{u} ⟶ Δ[1] := const (stdSimplex.obj₀Equiv.symm 1)

lemma ι₀_eq_rightUnitor_inv_comp_whiskerLeft (A : SSet.{u}) :
    (ι₀ : A ⟶ A ⊗ Δ[1]) = (ρ_ A).inv ≫ A ◁ pt₀ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [ι₀, pt₀]

lemma ι₁_eq_rightUnitor_inv_comp_whiskerLeft (A : SSet.{u}) :
    (ι₁ : A ⟶ A ⊗ Δ[1]) = (ρ_ A).inv ≫ A ◁ pt₁ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [ι₁, pt₁]

@[reassoc]
lemma pt₀_leftUnitor_inv_whiskerRight {W : SSet.{u}} (v : 𝟙_ SSet.{u} ⟶ W) :
    pt₀ ≫ (λ_ Δ[1]).inv ≫ v ▷ Δ[1] = v ≫ ι₀ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [ι₀, pt₀, -const_comp]

@[reassoc]
lemma pt₁_leftUnitor_inv_whiskerRight {W : SSet.{u}} (v : 𝟙_ SSet.{u} ⟶ W) :
    pt₁ ≫ (λ_ Δ[1]).inv ≫ v ▷ Δ[1] = v ≫ ι₁ := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [ι₁, pt₁, -const_comp]

/-- The homotopy `A ⊗ Δ[1] ⟶ X` over `B` given by an edge `𝟙_ SSet ⊗ Δ[1] ⟶ Map_B(A, X)`. -/
noncomputable def relMapHomotopy (K : 𝟙_ SSet.{u} ⊗ Δ[1] ⟶ relMap f r) : A ⊗ Δ[1] ⟶ X :=
  uncurry ((λ_ Δ[1]).inv ≫ K ≫ relMapFst f r)

/-- The homotopy given by an edge of `Map_B(A, X)` is a homotopy over `B`. -/
lemma relMapHomotopy_comp (K : 𝟙_ SSet.{u} ⊗ Δ[1] ⟶ relMap f r) :
    relMapHomotopy f r K ≫ r = fst A Δ[1] ≫ f := by
  have h : ((λ_ Δ[1]).inv ≫ K) ≫ relMapSnd f r = toUnit _ := toUnit_unique _ _
  rw [relMapHomotopy, ← uncurry_natural_right, Category.assoc, Category.assoc, relMapFst_map,
    ← Category.assoc, ← Category.assoc, h, uncurry_natural_left, pointOf, uncurry_curry,
    whiskerLeft_toUnit_comp_rightUnitor_hom_assoc]

lemma ι₀_relMapHomotopy (K : 𝟙_ SSet.{u} ⊗ Δ[1] ⟶ relMap f r) :
    ι₀ ≫ relMapHomotopy f r K = relMapHom f r (pt₀ ≫ (λ_ Δ[1]).inv ≫ K) := by
  rw [relMapHomotopy, relMapHom, ι₀_eq_rightUnitor_inv_comp_whiskerLeft, Category.assoc,
    ← uncurry_natural_left]
  simp only [Category.assoc]

lemma ι₁_relMapHomotopy (K : 𝟙_ SSet.{u} ⊗ Δ[1] ⟶ relMap f r) :
    ι₁ ≫ relMapHomotopy f r K = relMapHom f r (pt₁ ≫ (λ_ Δ[1]).inv ≫ K) := by
  rw [relMapHomotopy, relMapHom, ι₁_eq_rightUnitor_inv_comp_whiskerLeft, Category.assoc,
    ← uncurry_natural_left]
  simp only [Category.assoc]

end Vertices

/-! ### A cofinal right fibration has weakly contractible fibres -/

/-- A cofinal right fibration has weakly contractible fibres. -/
theorem weaklyContractible_fiber_of_isCofinal {Z C : SSet.{u}} (q : Z ⟶ C) [RightFibration q]
    (hq : IsCofinal q) (c : C _⦋0⦌) : WeaklyContractible (fiber q c) := by
  -- a homotopy inverse `g` of restriction along `q`, and the homotopy `g ≫ ρ ≃ 𝟙`
  obtain ⟨g, -, ⟨H⟩⟩ := hq Z q
  -- the vertex `𝟙 Z` of `Map_C(Z, Z)`
  let v : 𝟙_ SSet.{u} ⟶ relMap (q ≫ 𝟙 C) q :=
    relMapVertex (q ≫ 𝟙 C) q (𝟙 Z) (by rw [Category.id_comp, Category.comp_id])
  -- the section `s` of `q` classified by `g` applied to `𝟙 Z`
  let s : C ⟶ Z := relMapHom (𝟙 C) q (v ≫ g)
  have hs : s ≫ q = 𝟙 C := relMapHom_comp (𝟙 C) q (v ≫ g)
  -- the fibrewise homotopy `G` from `q ≫ s` to `𝟙 Z`, the homotopy `H` evaluated at `𝟙 Z`
  let G : Z ⊗ Δ[1] ⟶ Z := relMapHomotopy (q ≫ 𝟙 C) q (v ▷ Δ[1] ≫ H.h)
  have hG₀ : ι₀ ≫ G = q ≫ s := by
    rw [ι₀_relMapHomotopy, pt₀_leftUnitor_inv_whiskerRight_assoc, H.h₀, ← Category.assoc,
      relMapHom_comp_relMapRestrict]
  have hG₁ : ι₁ ≫ G = 𝟙 Z := by
    rw [ι₁_relMapHomotopy, pt₁_leftUnitor_inv_whiskerRight_assoc, H.h₁, Category.comp_id v,
      relMapHom_relMapVertex]
  have hGq : G ≫ q = fst Z Δ[1] ≫ q := by
    rw [relMapHomotopy_comp, Category.comp_id]
  -- restrict `G` to the fibre over `c`
  have hGc : (fiberι q c ▷ Δ[1] ≫ G) ≫ q = toUnit _ ≫ const c := by
    rw [Category.assoc, hGq, whiskerRight_fst_assoc, fiberι_comp_eq_const, comp_const,
      comp_const]
  let Gc : fiber q c ⊗ Δ[1] ⟶ fiber q c := pullback.lift (fiberι q c ▷ Δ[1] ≫ G) (toUnit _) hGc
  have hGc₁ : ι₁ ≫ Gc = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ι₁_comp_assoc, hG₁, Category.comp_id,
        Category.id_comp]
    · exact toUnit_unique _ _
  have hΦι : (ι₀ ≫ Gc) ≫ fiberι q c = const c ≫ s := by
    rw [Category.assoc, pullback.lift_fst, ι₀_comp_assoc, hG₀, ← Category.assoc,
      fiberι_comp_eq_const]
  -- the vertex `s(c)` of the fibre
  let y : 𝟙_ SSet.{u} ⟶ fiber q c :=
    pullback.lift (const c ≫ s) (𝟙 _)
      (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  let x : (fiber q c) _⦋0⦌ := unitHomEquiv _ y
  have hy : (const x : 𝟙_ SSet.{u} ⟶ fiber q c) = y := (unitHomEquiv _).symm_apply_apply y
  have hΦ : ι₀ ≫ Gc = const x := by
    apply pullback.hom_ext
    · rw [hΦι, ← comp_const (toUnit (fiber q c)) x, hy, Category.assoc, pullback.lift_fst,
        ← Category.assoc, comp_const]
    · exact toUnit_unique _ _
  exact weaklyContractible_of_homotopy_id_const (ι₀ ≫ Gc) x (Homotopy.mk' Gc rfl hGc₁)
    ((Homotopy.refl' _).ofEq' rfl hΦ)

end SSet
