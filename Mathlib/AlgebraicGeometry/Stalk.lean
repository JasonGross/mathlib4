/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Fangming Li
-/
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Stalks of a Scheme

## Main definitions and results

- `AlgebraicGeometry.Scheme.fromSpecStalk`: The canonical morphism `Spec 𝒪_{X, x} ⟶ X`.
- `AlgebraicGeometry.Scheme.range_fromSpecStalk`: The range of the map `Spec 𝒪_{X, x} ⟶ X` is
  exactly the `y` that specializes to `x`.
- `AlgebraicGeometry.SpecToEquivOfLocalRing`:
  Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
  `(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace LocalRing

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)

section fromSpecStalk

/--
A morphism from `Spec(O_x)` to `X`, which is defined with the help of an affine open
neighborhood `U` of `x`.
-/
noncomputable def IsAffineOpen.fromSpecStalk
    {x : X} (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  Spec.map (X.presheaf.germ ⟨x, hxU⟩) ≫ hU.fromSpec

/--
The morphism from `Spec(O_x)` to `X` given by `IsAffineOpen.fromSpec` does not depend on the affine
open neighborhood of `x` we choose.
-/
theorem IsAffineOpen.fromSpecStalk_eq (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    hU.fromSpecStalk hxU = hV.fromSpecStalk hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X) (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  transitivity fromSpecStalk h₁ h₂
  · rw [fromSpecStalk, fromSpecStalk, ← hU.map_fromSpec h₁ (homOfLE $ h₃.trans inf_le_left).op,
      ← Spec.map_comp_assoc, TopCat.Presheaf.germ_res]
  · rw [fromSpecStalk, fromSpecStalk, ← hV.map_fromSpec h₁ (homOfLE $ h₃.trans inf_le_right).op,
      ← Spec.map_comp_assoc, TopCat.Presheaf.germ_res]

/--
If `x` is a point of `X`, this is the canonical morphism from `Spec(O_x)` to `X`.
-/
noncomputable def Scheme.fromSpecStalk (X : Scheme.{u}) (x : X) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  (isAffineOpen_opensRange (X.affineOpenCover.map x)).fromSpecStalk (X.affineOpenCover.covers x)

@[simp]
theorem IsAffineOpen.fromSpecStalk_eq_fromSpecStalk {x : X} (hxU : x ∈ U) :
    hU.fromSpecStalk hxU = X.fromSpecStalk x := fromSpecStalk_eq ..

lemma IsAffineOpen.fromSpecStalk_closedPoint {U : Opens X} (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) :
    (hU.fromSpecStalk hxU).1.base (closedPoint (X.presheaf.stalk x)) = x := by
  rw [IsAffineOpen.fromSpecStalk, Scheme.comp_val_base_apply]
  erw [← hU.primeIdealOf_eq_map_closedPoint ⟨x, hxU⟩, hU.fromSpec_primeIdealOf ⟨x, hxU⟩]

namespace Scheme

@[simp]
lemma fromSpecStalk_closedPoint {x : X} :
    (X.fromSpecStalk x).1.base (closedPoint (X.presheaf.stalk x)) = x :=
  IsAffineOpen.fromSpecStalk_closedPoint _ _

lemma fromSpecStalk_app {x : X} (hxU : x ∈ U) :
    (X.fromSpecStalk x).app U =
      X.presheaf.germ ⟨x, hxU⟩ ≫
        (ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op := by
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ := (isBasis_affine_open X).exists_subset_of_mem_open
    hxU U.2
  have : V.ι ⁻¹ᵁ U = ⊤ := eq_top_iff.mpr fun x _ ↦ hVU x.2
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV, IsAffineOpen.fromSpecStalk, Scheme.comp_app,
    IsAffineOpen.fromSpec_app_of_le hV _ hVU, ←  X.presheaf.germ_res (homOfLE hVU) ⟨x, hxV⟩]
  simp only [Category.assoc]
  rw [Hom.naturality, ← ΓSpecIso_inv_naturality_assoc]
  rfl

@[reassoc]
lemma stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStalk x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxU : x ∈ U := h.mem_open U.2 hyU
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hyU, ← hU.fromSpecStalk_eq_fromSpecStalk hxU,
    IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpecStalk, ← Category.assoc, ← Spec.map_comp,
    TopCat.Presheaf.germ_stalkSpecializes]

@[reassoc (attr := simp)]
lemma stalkMap_fromSpecStalk {x} :
    Spec.map (PresheafedSpace.stalkMap f.1 x) ≫ Y.fromSpecStalk _ = X.fromSpecStalk x ≫ f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := (isBasis_affine_open Y).exists_subset_of_mem_open
    (Set.mem_univ (f.1.base x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := (isBasis_affine_open X).exists_subset_of_mem_open
    hxU (f ⁻¹ᵁ U).2
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, ← hV.fromSpecStalk_eq_fromSpecStalk hxV,
    IsAffineOpen.fromSpecStalk, ← Spec.map_comp_assoc, PresheafedSpace.stalkMap_germ f.1 _ ⟨x, hxU⟩,
    IsAffineOpen.fromSpecStalk, Spec.map_comp_assoc, ← X.presheaf.germ_res (homOfLE hVU) ⟨x, hxV⟩,
    Spec.map_comp_assoc, Category.assoc, ← Scheme.Hom.app, ← Spec.map_comp_assoc (f.app _),
      Hom.app_eq_appLE, Hom.appLE_map, IsAffineOpen.map_appLE_fromSpec]

lemma Spec_fromSpecStalk (R : CommRingCat) (x) :
    (Spec R).fromSpecStalk x =
      Spec.map ((ΓSpecIso R).inv ≫ (Spec R).presheaf.germ (U := ⊤) ⟨x, trivial⟩) := by
  rw [← (isAffineOpen_top (Spec R)).fromSpecStalk_eq_fromSpecStalk (x := x) trivial,
    IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpec_top, isoSpec_Spec_inv,
    ← Spec.map_comp]

-- This is not a simp lemma to respect the abstraction boundaries
lemma Spec_fromSpecStalk' (R : CommRingCat) (x) :
    (Spec R).fromSpecStalk x = Spec.map (StructureSheaf.toStalk R _) :=
  Spec_fromSpecStalk _ _

/-- https://stacks.math.columbia.edu/tag/01J7 -/
lemma range_fromSpecStalk {x : X} :
    Set.range (X.fromSpecStalk x).1.base = { y | y ⤳ x } := by
  ext y
  constructor
  · rintro ⟨y, rfl⟩
    exact ((LocalRing.specializes_closedPoint y).map (X.fromSpecStalk x).1.base.2).trans
      (specializes_of_eq fromSpecStalk_closedPoint)
  · rintro (hy : y ⤳ x)
    have := fromSpecStalk_closedPoint (x := y)
    rw [← stalkSpecializes_fromSpecStalk hy] at this
    exact ⟨_, this⟩

end Scheme

end fromSpecStalk

variable (R : CommRingCat.{u}) [LocalRing R]

section stalkClosedPointIso

/-- For a local ring `(R, 𝔪)`,
this is the isomorphism between the stalk of `Spec R` at `𝔪` and `R`. -/
noncomputable
def stalkClosedPointIso :
    (Spec R).presheaf.stalk (closedPoint R) ≅ R :=
  StructureSheaf.stalkIso _ _ ≪≫ (IsLocalization.atUnits R
      (closedPoint R).asIdeal.primeCompl fun _ ↦ not_not.mp).toRingEquiv.toCommRingCatIso.symm

lemma stalkClosedPointIso_inv :
    (stalkClosedPointIso R).inv = StructureSheaf.toStalk R _ := by
  ext x
  exact StructureSheaf.localizationToStalk_of _ _ _

lemma ΓSpecIso_hom_stalkClosedPointIso_inv :
    (Scheme.ΓSpecIso R).hom ≫ (stalkClosedPointIso R).inv =
      (Spec R).presheaf.germ (U := ⊤) ⟨closedPoint _, trivial⟩ := by
  rw [stalkClosedPointIso_inv, ← Iso.eq_inv_comp]
  rfl

@[reassoc (attr := simp)]
lemma germ_stalkClosedPointIso_hom :
    (Spec R).presheaf.germ (U := ⊤) ⟨closedPoint _, trivial⟩ ≫ (stalkClosedPointIso R).hom =
      (Scheme.ΓSpecIso R).hom := by
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma Spec_stalkClosedPointIso :
    Spec.map (stalkClosedPointIso R).inv = (Spec R).fromSpecStalk (closedPoint R) := by
  rw [stalkClosedPointIso_inv, Scheme.Spec_fromSpecStalk']

end stalkClosedPointIso

section stalkClosedPointTo

variable {R} (f : Spec R ⟶ X)

-- move me
lemma LocalRing.closed_point_mem_iff {R : Type*} [CommRing R] [LocalRing R]
    {U : Opens (PrimeSpectrum R)} : closedPoint R ∈ U ↔ U = ⊤ :=
  ⟨(eq_top_iff.mpr fun x _ ↦ (specializes_closedPoint x).mem_open U.2 ·), (· ▸ trivial)⟩

@[simp]
lemma Spec_closedPoint {R S : CommRingCat} [LocalRing R] [LocalRing S]
    {f : R ⟶ S} [IsLocalRingHom f] : (Spec.map f).1.base (closedPoint S) = closedPoint R :=
  LocalRing.comap_closedPoint f

namespace Scheme

/--
Given a local ring `(R, 𝔪)` and a morphism `f : Spec R ⟶ X`,
they induce a ring homomorphim `φ : 𝒪_{X, f 𝔪} ⟶ X`.

This is inverse to `φ ↦ Spec.map φ ≫ X.fromSpecStalk (f 𝔪)`. See `SpecToEquivOfLocalRing`.
-/
noncomputable
def stalkClosedPointTo :
    X.presheaf.stalk (f.1.base (closedPoint R)) ⟶ R :=
  PresheafedSpace.stalkMap f.1 (closedPoint R) ≫ (stalkClosedPointIso R).hom

instance isLocalRingHom_stalkClosedPointTo :
    IsLocalRingHom (stalkClosedPointTo f) := by
  delta stalkClosedPointTo; infer_instance

lemma preimage_eq_top_of_closedPoint_mem
    {U : Opens X} (hU : f.1.base (closedPoint R) ∈ U) : f ⁻¹ᵁ U = ⊤ :=
  LocalRing.closed_point_mem_iff.mp hU

lemma stalkClosedPointTo_comp (g : X ⟶ Y) :
    stalkClosedPointTo (f ≫ g) = PresheafedSpace.stalkMap g.1 _ ≫ stalkClosedPointTo f := by
  rw [stalkClosedPointTo]
  erw [PresheafedSpace.stalkMap.comp]
  exact Category.assoc _ _ _

lemma germ_stalkClosedPointTo_Spec {R S : CommRingCat} [LocalRing S] (φ : R ⟶ S):
    (Spec R).presheaf.germ (U := ⊤) ⟨_, trivial⟩ ≫ stalkClosedPointTo (Spec.map φ) =
      (ΓSpecIso R).hom ≫ φ := by
  rw [stalkClosedPointTo, PresheafedSpace.stalkMap_germ'_assoc, ← Iso.inv_comp_eq,
    ← ΓSpecIso_inv_naturality_assoc, germ_stalkClosedPointIso_hom, Iso.inv_hom_id,
    Category.comp_id]

@[reassoc]
lemma germ_stalkClosedPointTo (U : Opens X) (hU : f.1.base (closedPoint R) ∈ U) :
    X.presheaf.germ ⟨_, hU⟩ ≫ stalkClosedPointTo f = f.app U ≫
      ((Spec R).presheaf.mapIso (eqToIso (preimage_eq_top_of_closedPoint_mem f hU).symm).op ≪≫
        ΓSpecIso R).hom := by
  rw [stalkClosedPointTo, PresheafedSpace.stalkMap_germ'_assoc, Iso.trans_hom]
  congr 1
  rw [← Iso.eq_comp_inv, Category.assoc, ΓSpecIso_hom_stalkClosedPointIso_inv]
  simp only [TopCat.Presheaf.pushforward_obj_obj, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    TopCat.Presheaf.germ_res]

@[reassoc]
lemma germ_stalkClosedPointTo_Spec_fromSpecStalk
    {x : X} (f : X.presheaf.stalk x ⟶ R) [IsLocalRingHom f] (U : Opens X) (hU) :
    X.presheaf.germ (U := U) ⟨_, hU⟩ ≫ stalkClosedPointTo (Spec.map f ≫ X.fromSpecStalk x) =
      X.presheaf.germ (U := U) ⟨x, by simpa using hU⟩ ≫ f := by
  have : (Spec.map f ≫ X.fromSpecStalk x).1.base (closedPoint R) = x := by
    rw [comp_val_base_apply, Spec_closedPoint, fromSpecStalk_closedPoint]
  have : x ∈ U := this ▸ hU
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc,
    germ_stalkClosedPointTo, comp_app,
    fromSpecStalk_app (X := X) (x := x) this, Category.assoc, Iso.trans_hom,
    Functor.mapIso_hom, Hom.naturality_assoc, ← Functor.map_comp_assoc,
    (Spec.map f).app_eq_appLE, Hom.appLE_map_assoc, Hom.map_appLE_assoc]
  erw [← (Spec.map f).app_eq_appLE]
  rw [ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

lemma stalkClosedPointTo_fromSpecStalk (x : X) :
    stalkClosedPointTo (X.fromSpecStalk x) =
      (X.presheaf.stalkCongr (by rw [fromSpecStalk_closedPoint]; rfl)).hom := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes, id_eq]
  have : X.fromSpecStalk x = Spec.map (𝟙 (X.presheaf.stalk x)) ≫ X.fromSpecStalk x := by simp
  convert germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 (X.presheaf.stalk x)) U hxU

@[reassoc]
lemma Spec_stalkClosedPointTo_fromSpecStalk :
    Spec.map (stalkClosedPointTo f) ≫ X.fromSpecStalk _ = f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := (isBasis_affine_open X).exists_subset_of_mem_open
    (Set.mem_univ (f.1.base (closedPoint R))) isOpen_univ
  have := IsAffineOpen.map_appLE_fromSpec f hU (isAffineOpen_top _)
    (preimage_eq_top_of_closedPoint_mem f hxU).ge
  rw [IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, isoSpec_Spec_hom] at this
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, ← Spec.map_comp_assoc,
    germ_stalkClosedPointTo]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    Hom.app_eq_appLE, Hom.appLE_map_assoc, Spec.map_comp_assoc]

end Scheme

end stalkClosedPointTo

variable {R}

/-- useful lemma for applications of `SpecToEquivOfLocalRing` -/
lemma SpecToEquivOfLocalRing_eq_iff
    {f₁ f₂ : Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalRingHom f }} :
    f₁ = f₂ ↔ ∃ h₁ : f₁.1 = f₂.1, f₁.2.1 =
      (X.presheaf.stalkCongr (by rw [h₁]; rfl)).hom ≫ f₂.2.1 := by
  constructor
  · rintro rfl; simp
  · obtain ⟨x₁, ⟨f₁, h₁⟩⟩ := f₁
    obtain ⟨x₂, ⟨f₂, h₂⟩⟩ := f₂
    rintro ⟨rfl : x₁ = x₂, e : f₁ = _⟩
    simp [e]

variable (X R)

/--
Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
`(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/
noncomputable
def SpecToEquivOfLocalRing :
    (Spec R ⟶ X) ≃ Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalRingHom f } where
  toFun f := ⟨f.1.base (closedPoint R), Scheme.stalkClosedPointTo f, inferInstance⟩
  invFun xf := Spec.map xf.2.1 ≫ X.fromSpecStalk xf.1
  left_inv := Scheme.Spec_stalkClosedPointTo_fromSpecStalk
  right_inv xf := by
    obtain ⟨x, ⟨f, hf⟩⟩ := xf
    symm
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨?_, ?_⟩
    · simp only [Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply, Spec_closedPoint,
        Scheme.fromSpecStalk_closedPoint]
    · refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
      simp only [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk,
        TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc]

end AlgebraicGeometry
