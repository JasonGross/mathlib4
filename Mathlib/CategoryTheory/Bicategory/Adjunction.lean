/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.CategoryTheory.Bicategory.Coherence
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# Adjunctions in bicategories

For 1-morphisms `f : a ⟶ b` and `g : b ⟶ a` in a bicategory, an adjunction between `f` and `g`
consists of a pair of 2-morphism `η : 𝟙 a ⟶ f ≫ g` and `ε : g ≫ f ⟶ 𝟙 b` satisfying the triangle
identities. The 2-morphism `η` is called the unit and `ε` is called the counit.

## Main definitions

* `Bicategory.Adjunction`: adjunctions between two 1-morphisms.
* `Bicategory.Equivalence`: adjoint equivalences between two objects.
* `Bicategory.mkOfAdjointifyCounit`: construct an adjoint equivalence from 2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `ε` to a counit.

## Implementation notes

The computation of 2-morphisms in the proof is done using `calc` blocks. Typically,
the LHS and the RHS in each step of `calc` are related by simple rewriting up to associators
and unitors. So the proof for each step should be of the form `rw [...]; coherence`. In practice,
our proofs look like `rw [...]; simp [bicategoricalComp]; coherence`. The `simp` is not strictly
necessary, but it speeds up the proof and allow us to avoid increasing the `maxHeartbeats`.
The speedup is probably due to reducing the length of the expression e.g. by absorbing
identity maps or applying the pentagon relation. Such a hack may not be necessary if the
coherence tactic is improved. One possible way would be to perform such a simplification in the
preprocessing of the coherence tactic.

## Todo

* `Bicategory.mkOfAdjointifyUnit`: construct an adjoint equivalence from 2-isomorphisms
  `η : 𝟙 a ≅ f ≫ g` and `ε : g ≫ f ≅ 𝟙 b`, by upgrading `η` to a unit.
-/

namespace CategoryTheory

namespace Bicategory

open Category

open scoped Bicategory

open Mathlib.Tactic.BicategoryCoherence (bicategoricalComp bicategoricalIsoComp)

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B} {f : a ⟶ b} {g : b ⟶ a}

/-- The 2-morphism defined by the following pasting diagram:
```
a －－－－－－ ▸ a
  ＼    η      ◥   ＼
  f ＼   g  ／       ＼ f
       ◢  ／     ε      ◢
        b －－－－－－ ▸ b
```
-/
def leftZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  η ▷ f ⊗≫ f ◁ ε

/-- The 2-morphism defined by the following pasting diagram:
```
        a －－－－－－ ▸ a
       ◥  ＼     η      ◥
  g ／      ＼ f     ／ g
  ／    ε      ◢   ／
b －－－－－－ ▸ b
```
-/
def rightZigzag (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :=
  g ◁ η ⊗≫ ε ▷ g

theorem rightZigzag_idempotent_of_left_triangle
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) (h : leftZigzag η ε = (λ_ _).hom ≫ (ρ_ _).inv) :
    rightZigzag η ε ⊗≫ rightZigzag η ε = rightZigzag η ε := by
  dsimp only [rightZigzag]
  calc
    _ = g ◁ η ⊗≫ ((ε ▷ g ▷ 𝟙 a) ≫ (𝟙 b ≫ g) ◁ η) ⊗≫ ε ▷ g := by
      simp [bicategoricalComp]; coherence
    _ = 𝟙 _ ⊗≫ g ◁ (η ▷ 𝟙 a ≫ (f ≫ g) ◁ η) ⊗≫ (ε ▷ (g ≫ f) ≫ 𝟙 b ◁ ε) ▷ g ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; simp [bicategoricalComp]; coherence
    _ = g ◁ η ⊗≫ g ◁ leftZigzag η ε ▷ g ⊗≫ ε ▷ g := by
      rw [← whisker_exchange,  ← whisker_exchange]; simp [leftZigzag, bicategoricalComp]; coherence
    _ = g ◁ η ⊗≫ ε ▷ g := by
      rw [h]; simp [bicategoricalComp]; coherence

/-- Adjunction between two 1-morphisms. -/
structure Adjunction (f : a ⟶ b) (g : b ⟶ a) where
  /-- The unit of an adjunction. -/
  unit : 𝟙 a ⟶ f ≫ g
  /-- The counit of an adjunction. -/
  counit : g ≫ f ⟶ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzag unit counit = (λ_ _).hom ≫ (ρ_ _).inv := by aesop_cat
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  right_triangle : rightZigzag unit counit = (ρ_ _).hom ≫ (λ_ _).inv := by aesop_cat

@[inherit_doc] scoped infixr:15 " ⊣ " => Bicategory.Adjunction

namespace Adjunction

attribute [simp] left_triangle right_triangle

attribute [local simp] leftZigzag rightZigzag

/-- Adjunction between identities. -/
def id (a : B) : 𝟙 a ⊣ 𝟙 a where
  unit := (ρ_ _).inv
  counit := (ρ_ _).hom
  left_triangle := by dsimp; coherence
  right_triangle := by dsimp; coherence

instance : Inhabited (Adjunction (𝟙 a) (𝟙 a)) :=
  ⟨id a⟩

section Composition

variable {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- Auxiliary definition for `adjunction.comp`. -/
@[simp]
def compUnit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁ :=
  adj₁.unit ⊗≫ f₁ ◁ adj₂.unit ▷ g₁ ⊗≫ 𝟙 _

/-- Auxiliary definition for `adjunction.comp`. -/
@[simp]
def compCounit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c :=
  𝟙 _ ⊗≫ g₂ ◁ adj₁.counit ▷ f₂ ⊗≫ adj₂.counit

theorem comp_left_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    leftZigzag (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (λ_ _).hom ≫ (ρ_ _).inv := by
  calc
    _ = 𝟙 _ ⊗≫
          adj₁.unit ▷ (f₁ ≫ f₂) ⊗≫
            f₁ ◁ (adj₂.unit ▷ (g₁ ≫ f₁) ≫ (f₂ ≫ g₂) ◁ adj₁.counit) ▷ f₂ ⊗≫
              (f₁ ≫ f₂) ◁ adj₂.counit ⊗≫ 𝟙 _ := by
      simp [bicategoricalComp]; coherence
    _ = 𝟙 _ ⊗≫
          (leftZigzag adj₁.unit adj₁.counit) ▷ f₂ ⊗≫
            f₁ ◁ (leftZigzag adj₂.unit adj₂.counit) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; simp [bicategoricalComp]; coherence
    _ = _ := by
      simp_rw [left_triangle]; simp [bicategoricalComp]

theorem comp_right_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    rightZigzag (compUnit adj₁ adj₂) (compCounit adj₁ adj₂) = (ρ_ _).hom ≫ (λ_ _).inv := by
  calc
    _ = 𝟙 _ ⊗≫
          (g₂ ≫ g₁) ◁ adj₁.unit ⊗≫
            g₂ ◁ ((g₁ ≫ f₁) ◁ adj₂.unit ≫ adj₁.counit ▷ (f₂ ≫ g₂)) ▷ g₁ ⊗≫
              adj₂.counit ▷ (g₂ ≫ g₁) ⊗≫ 𝟙 _ := by
      simp [bicategoricalComp]; coherence
    _ = 𝟙 _ ⊗≫
          g₂ ◁ (rightZigzag adj₁.unit adj₁.counit) ⊗≫
            (rightZigzag adj₂.unit adj₂.counit) ▷ g₁ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]; simp [bicategoricalComp]; coherence
    _ = _ := by
      simp_rw [right_triangle]; simp [bicategoricalComp]

/-- Composition of adjunctions. -/
@[simps]
def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : f₁ ≫ f₂ ⊣ g₂ ≫ g₁ where
  unit := compUnit adj₁ adj₂
  counit := compCounit adj₁ adj₂
  left_triangle := by apply comp_left_triangle_aux
  right_triangle := by apply comp_right_triangle_aux

end Composition

end Adjunction

noncomputable section

variable (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b)

/-- The isomorphism version of `leftZigzag`. -/
def leftZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerRightIso η f ≪⊗≫ whiskerLeftIso f ε

/-- The isomorphism version of `rightZigzag`. -/
def rightZigzagIso (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :=
  whiskerLeftIso g η ≪⊗≫ whiskerRightIso ε g

attribute [local simp] leftZigzagIso rightZigzagIso leftZigzag rightZigzag

@[simp]
theorem leftZigzagIso_hom : (leftZigzagIso η ε).hom = leftZigzag η.hom ε.hom :=
  rfl

@[simp]
theorem rightZigzagIso_hom : (rightZigzagIso η ε).hom = rightZigzag η.hom ε.hom :=
  rfl

@[simp]
theorem leftZigzagIso_inv : (leftZigzagIso η ε).inv = rightZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
theorem rightZigzagIso_inv : (rightZigzagIso η ε).inv = leftZigzag ε.inv η.inv := by
  simp [bicategoricalComp, bicategoricalIsoComp]

@[simp]
theorem leftZigzagIso_symm : (leftZigzagIso η ε).symm = rightZigzagIso ε.symm η.symm :=
  Iso.ext (leftZigzagIso_inv η ε)

@[simp]
theorem rightZigzagIso_symm : (rightZigzagIso η ε).symm = leftZigzagIso ε.symm η.symm :=
  Iso.ext (rightZigzagIso_inv η ε)

instance : IsIso (leftZigzag η.hom ε.hom) := inferInstanceAs <| IsIso (leftZigzagIso η ε).hom

instance : IsIso (rightZigzag η.hom ε.hom) := inferInstanceAs <| IsIso (rightZigzagIso η ε).hom

theorem right_triangle_of_left_triangle (h : leftZigzag η.hom ε.hom = (λ_ f).hom ≫ (ρ_ f).inv) :
    rightZigzag η.hom ε.hom = (ρ_ g).hom ≫ (λ_ g).inv := by
  rw [← cancel_epi (rightZigzag η.hom ε.hom ≫ (λ_ g).hom ≫ (ρ_ g).inv)]
  calc
    _ = rightZigzag η.hom ε.hom ⊗≫ rightZigzag η.hom ε.hom := by coherence
    _ = rightZigzag η.hom ε.hom := rightZigzag_idempotent_of_left_triangle _ _ h
    _ = _ := by simp

/-- An auxiliary definition for `mkOfAdjointifyCounit`. -/
def adjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : g ≫ f ≅ 𝟙 b :=
  whiskerLeftIso g ((ρ_ f).symm ≪≫ rightZigzagIso ε.symm η.symm ≪≫ λ_ f) ≪≫ ε

theorem adjointifyCounit_left_triangle (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) :
    leftZigzagIso η (adjointifyCounit η ε) = λ_ f ≪≫ (ρ_ f).symm := by
  apply Iso.ext
  dsimp [adjointifyCounit, bicategoricalIsoComp]
  calc
    _ = 𝟙 _ ⊗≫ (η.hom ▷ (f ≫ 𝟙 b) ≫ (f ≫ g) ◁ f ◁ ε.inv) ⊗≫
          f ◁ g ◁ η.inv ▷ f ⊗≫ f ◁ ε.hom := by
      simp [bicategoricalComp]; coherence
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.hom ▷ (f ≫ g) ≫ (f ≫ g) ◁ η.inv) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom (f ◁ ε.inv)]; simp [bicategoricalComp]; coherence
    _ = 𝟙 _ ⊗≫ f ◁ ε.inv ⊗≫ (η.inv ≫ η.hom) ▷ f ⊗≫ f ◁ ε.hom := by
      rw [← whisker_exchange η.hom η.inv]; coherence
    _ = 𝟙 _ ⊗≫ f ◁ (ε.inv ≫ ε.hom) := by
      rw [Iso.inv_hom_id]; simp [bicategoricalComp]
    _ = _ := by
      rw [Iso.inv_hom_id]; simp [bicategoricalComp]

/-- Adjoint equivalences between two objects. -/
structure Equivalence (a b : B) where
  /-- A 1-morphism in one direction. -/
  hom : a ⟶ b
  /-- A 1-morphism in the other direction. -/
  inv : b ⟶ a
  /-- The composition `hom ≫ inv` is isomorphic to the identity. -/
  unit : 𝟙 a ≅ hom ≫ inv
  /-- The composition `inv ≫ hom` is isomorphic to the identity. -/
  counit : inv ≫ hom ≅ 𝟙 b
  /-- The composition of the unit and the counit is equal to the identity up to unitors. -/
  left_triangle : leftZigzagIso unit counit = λ_ hom ≪≫ (ρ_ hom).symm := by aesop_cat

@[inherit_doc] scoped infixr:10 " ≌ " => Bicategory.Equivalence

namespace Equivalence

/-- The identity 1-morphism is an equivalence. -/
def id (a : B) : a ≌ a := ⟨_, _, (ρ_ _).symm, ρ_ _, by ext; simp [bicategoricalIsoComp]⟩

instance : Inhabited (Equivalence a a) := ⟨id a⟩

theorem left_triangle_hom (e : a ≌ b) :
    leftZigzag e.unit.hom e.counit.hom = (λ_ e.hom).hom ≫ (ρ_ e.hom).inv :=
  congrArg Iso.hom e.left_triangle

theorem right_triangle (e : a ≌ b) :
    rightZigzagIso e.unit e.counit = ρ_ e.inv ≪≫ (λ_ e.inv).symm :=
  Iso.ext (right_triangle_of_left_triangle e.unit e.counit e.left_triangle_hom)

theorem right_triangle_hom (e : a ≌ b) :
    rightZigzag e.unit.hom e.counit.hom = (ρ_ e.inv).hom ≫ (λ_ e.inv).inv :=
  congrArg Iso.hom e.right_triangle

/-- Construct an adjoint equivalence from 2-isomorphisms by upgrading `ε` to a counit. -/
def mkOfAdjointifyCounit (η : 𝟙 a ≅ f ≫ g) (ε : g ≫ f ≅ 𝟙 b) : a ≌ b where
  hom := f
  inv := g
  unit := η
  counit := adjointifyCounit η ε
  left_triangle := adjointifyCounit_left_triangle η ε

end Equivalence

end

section Pseudofunctor

noncomputable section

universe w' v' u'

variable {C : Type u'} [Bicategory.{w', v'} C]

def Pseudofunctor.mapAdjunction (F : Pseudofunctor B C) (adj : Bicategory.Adjunction f g) :
    Bicategory.Adjunction (F.map f) (F.map g) where
  unit := (F.mapId a).inv ≫ (F.map₂ adj.unit) ≫ (F.mapComp f g).hom
  counit := (F.mapComp g f).inv ≫ (F.map₂ adj.counit) ≫ (F.mapId b).hom
  left_triangle := by
    simp only [leftZigzag, comp_whiskerRight, whiskerLeft_comp]
    have := F.map₂_whisker_right adj.unit f
    apply_fun (fun x ↦ (F.mapComp (𝟙 a) f).inv ≫ x ≫ (F.mapComp (f ≫ g) f).hom) at this
    simp only [assoc, Iso.inv_hom_id, comp_id, Iso.inv_hom_id_assoc] at this
    rw [← this]
    have := F.map₂_whisker_left f adj.counit
    apply_fun (fun x ↦ (F.mapComp f (g ≫ f)).inv ≫ x ≫ (F.mapComp f (𝟙 b)).hom) at this
    simp only [assoc, Iso.inv_hom_id, comp_id, Iso.inv_hom_id_assoc] at this
    rw [← this]
    simp only [bicategoricalComp, assoc, Iso.inv_hom_id, comp_id,
      Iso.inv_hom_id_assoc, Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom', whiskerRight_comp,
      id_whiskerRight, id_comp]
    have := F.map₂_associator f g f
    repeat (rw [← Category.assoc] at this)
    rw [← Category.assoc ((F.mapId a).inv ▷ F.map f) _ _]
    rw [← Category.assoc _ (F.map₂ (adj.unit ▷ f)) _]
    rw [← Category.assoc (F.mapComp (f ≫ g) f).hom _ _]
    rw [← Category.assoc _ ((α_ (F.map f) (F.map g) (F.map f)).hom) _]
    rw [← Category.assoc _ (F.map f ◁ (F.mapComp g f).inv) _]
    rw [← Category.assoc _ ((F.mapComp f (g ≫ f)).inv) _]
    rw [← this]
    simp only [Category.assoc]
    rw [← Category.assoc ((F.mapId a).inv ▷ F.map f) _ _]
    rw [← Category.assoc (F.map₂ (adj.unit ▷ f)) _ _]
    rw [← Category.assoc _ (F.map₂ (f ◁ adj.counit)) _]
    rw [← F.map₂_comp, ← F.map₂_comp]
    have := adj.left_triangle
    simp only [leftZigzag, bicategoricalComp,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom', whiskerRight_comp,
      id_whiskerRight, id_comp, Iso.inv_hom_id, comp_id] at this
    rw [← Category.assoc] at this
    rw [this]
    simp only [Pseudofunctor.map₂_comp, assoc, Iso.inv_hom_id_assoc,
      inv_hom_whiskerRight_assoc]
    simp only [Pseudofunctor.map₂_left_unitor, assoc, Iso.inv_hom_id_assoc,
      inv_hom_whiskerRight_assoc, Iso.cancel_iso_hom_left]
    have : IsIso (F.map₂ (ρ_ f).hom) := OplaxFunctor.map₂_isIso F.toOplax _
    have : F.map₂ (ρ_ f).inv = inv (F.map₂ (ρ_ f).hom) := by
      rw [← IsIso.Iso.inv_hom]
      exact F.toOplax.map₂_inv (ρ_ f).hom
    rw [this]
    simp only [Pseudofunctor.map₂_right_unitor, IsIso.inv_comp, IsIso.Iso.inv_hom, inv_whiskerLeft,
      assoc, Iso.inv_hom_id_assoc, whiskerLeft_inv_hom, comp_id]
  right_triangle := by
    simp only [rightZigzag, whiskerLeft_comp, comp_whiskerRight]
    have := F.map₂_whisker_left g adj.unit
    apply_fun (fun x ↦ (F.mapComp g (𝟙 a)).inv ≫ x ≫ (F.mapComp g (f ≫ g)).hom) at this
    simp only [assoc, Iso.inv_hom_id, comp_id, Iso.inv_hom_id_assoc] at this
    rw [← this]
    have := F.map₂_whisker_right adj.counit g
    apply_fun (fun x ↦ (F.mapComp (g ≫ f) g).inv ≫ x ≫ (F.mapComp (𝟙 b) g).hom) at this
    simp only [assoc, Iso.inv_hom_id, comp_id, Iso.inv_hom_id_assoc] at this
    rw [← this]
    simp only [bicategoricalComp, assoc, Iso.inv_hom_id, comp_id,
      Iso.inv_hom_id_assoc, Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom', whiskerRight_comp,
      id_whiskerRight, id_comp]
    have := F.toOplax.map₂_associator g f g
    rw [← IsIso.eq_inv_comp] at this
    simp only [Pseudofunctor.to_oplax_obj, Pseudofunctor.to_oplax_mapComp] at this
    conv_rhs at this => congr; change inv (F.toOplax.map₂Iso (α_ g f g)).hom; rw [IsIso.Iso.inv_hom]
    conv_rhs at this =>
      rw [← Category.assoc, ← Category.assoc]
    rw [← IsIso.comp_inv_eq, IsIso.Iso.inv_hom] at this
    repeat (rw [← Category.assoc] at this)
    rw [← Category.assoc (F.map g ◁ (F.mapId a).inv) _ _]
    rw [← Category.assoc _ (F.map₂ (g ◁ adj.unit)) _]
    rw [← Category.assoc (F.mapComp g (f ≫ g)).hom _ _]
    rw [← Category.assoc _ (α_ (F.map g) (F.map f) (F.map g)).inv _]
    erw [this]
    simp only [assoc, Iso.inv_hom_id_assoc, Pseudofunctor.to_oplax_obj, OplaxFunctor.map₂Iso_inv]
    slice_lhs 6 7 => erw [← comp_whiskerRight]; rw [Iso.hom_inv_id, id_whiskerRight]
    rw [Category.id_comp]
    slice_lhs 5 6 => rw [Iso.hom_inv_id]
    rw [Category.id_comp]
    slice_lhs 3 4 => erw [← F.map₂_comp]
    slice_lhs 3 4 => rw [← F.map₂_comp]
    have := adj.right_triangle
    simp only [rightZigzag, bicategoricalComp,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom,
      Mathlib.Tactic.BicategoryCoherence.BicategoricalCoherence.hom', whiskerRight_comp,
      id_whiskerRight, id_comp, Iso.inv_hom_id] at this
    rw [← Category.assoc] at this
    rw [this]
    simp only [Pseudofunctor.map₂_comp, Pseudofunctor.map₂_right_unitor, assoc,
      Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc, Iso.cancel_iso_hom_left]
    have : IsIso (F.map₂ (λ_ g).hom) := OplaxFunctor.map₂_isIso F.toOplax _
    have : F.map₂ (λ_ g).inv = inv (F.map₂ (λ_ g).hom) := by
      rw [← IsIso.Iso.inv_hom]
      exact F.toOplax.map₂_inv (λ_ g).hom
    rw [this]
    simp only [Pseudofunctor.map₂_left_unitor, IsIso.inv_comp, IsIso.Iso.inv_hom, inv_whiskerRight,
      assoc, Iso.inv_hom_id_assoc, inv_hom_whiskerRight, comp_id]

end

end Pseudofunctor

end Bicategory

end CategoryTheory
