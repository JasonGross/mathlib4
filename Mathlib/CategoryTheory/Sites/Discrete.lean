/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.DenseSubsite
import Mathlib.CategoryTheory.Sites.PreservesSheafification
/-!

# Discrete objects in sheaf categories.

This file defines the notion of a discrete object in a sheaf category. A discrete sheaf in this
context is a sheaf `F` such that the counit `(F(*))^cst ⟶ F` is an isomorphism. Here `*` denotes
a particular chosen terminal object of the defining site, and `cst` denotes the constant sheaf.

It is convenient to take an arbitrary terminal object; one might want to use this construction to
talk about discrete sheaves on a site which has a particularly convenient terminal object, such as
the one element space in `CompHaus`.

## Main results

* `isDiscrete_iff_mem_essImage` : A sheaf is discrete if and only if it is in the essential image
of the constant sheaf functor, if the constant sheaf functor is fully faithful.
* `isDiscrete_iff_of_equivalence` : The property of a sheaf of being discrete is invariant under
equivalence of sheaf categories, if the constant sheaf functor is fully faithful (the assumption
on the constant sheaf functor is probably unnecessary, but it's low priority to prove this in more
generality, because in all cases of interest, the assumption holds).
* `isDiscrete_iff_forget` : Given a "forgetful" functor `U : A ⥤ B` a sheaf `F : Sheaf J A` is
discrete if and only if the sheaf given by postcomposition with `U` is discrete.

## Future work

* Use `isDiscrete_iff_forget` to prove that a condensed module is discrete if and only if its
underlying condensed set is discrete.
-/

open CategoryTheory Limits Functor Adjunction Opposite Category Functor

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {A : Type*} [Category A]
  [HasWeakSheafify J A] {t : C} (ht : IsTerminal t)

/--
A sheaf is discrete if it is a discrete object of the "underlying object" functor from the sheaf
category to the target category.
-/
abbrev IsDiscrete (F : Sheaf J A) : Prop := IsIso ((constantSheafAdj J A ht).counit.app F)

lemma isDiscrete_iff_isIso_counit_app {L : A ⥤ Sheaf J A} (adj : L ⊣ (sheafSections J A).obj ⟨t⟩)
    (F : Sheaf J A) :
    IsDiscrete J ht F ↔ IsIso (adj.counit.app F) := by
  let i : L ≅ constantSheaf J A := adj.leftAdjointUniq (constantSheafAdj _ _ ht)
  have h : adj.counit.app F = i.hom.app _ ≫ (constantSheafAdj J A ht).counit.app F := by
    rw [← leftAdjointUniq_hom_counit]
    rfl
  constructor
  · intro
    rw [h]
    infer_instance
  · intro hh
    rw [h] at hh
    exact IsIso.of_isIso_comp_left (i.hom.app _) ((constantSheafAdj J A ht).counit.app F)

lemma isDiscrete_congr {F G : Sheaf J A} (i : F ≅ G) [IsDiscrete J ht F] : IsDiscrete J ht G := by
  have : IsIso ((constantSheaf J A).map (((sheafSections J A).obj ⟨t⟩).map i.inv) ≫
    ((constantSheafAdj J A ht).counit.app F) ≫ i.hom) := inferInstance
  convert this
  simp [-flip_obj_obj, -flip_obj_map]

section
lemma isDiscrete_of_iso [(constantSheaf J A).Faithful] [(constantSheaf J A).Full]
    {F : Sheaf J A} {X : A} (i : F ≅ (constantSheaf J A).obj X) : IsDiscrete J ht F :=
  isIso_counit_app_of_iso _ i

lemma isDiscrete_iff_mem_essImage (F : Sheaf J A)
    [(constantSheaf J A).Faithful] [(constantSheaf J A).Full] :
    F.IsDiscrete J ht ↔ F ∈ (constantSheaf J A).essImage :=
  (constantSheafAdj J A ht).isIso_counit_app_iff_mem_essImage

lemma isDiscrete_iff_mem_essImage' {L : A ⥤ Sheaf J A} (adj : L ⊣ (sheafSections J A).obj ⟨t⟩)
    [L.Faithful] [L.Full] (F : Sheaf J A) : IsDiscrete J ht F ↔ F ∈ L.essImage := by
  rw [isDiscrete_iff_isIso_counit_app _ _ adj]
  exact adj.isIso_counit_app_iff_mem_essImage

section Equivalence

variable {D : Type*} [Category D] (K : GrothendieckTopology D) [HasWeakSheafify K A]
variable (G : C ⥤ D)
  [∀ (X : Dᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) A]
  [G.IsDenseSubsite J K] (ht' : IsTerminal (G.obj t))

open Functor.IsDenseSubsite

noncomputable example :
    let e : Sheaf J A ≌ Sheaf K A :=
      sheafEquiv G J K A
    e.inverse ⋙ (sheafSections J A).obj (op t) ≅ (sheafSections K A).obj (op (G.obj t)) :=
  Iso.refl _

variable (A) in
/--
The constant sheaf functor commutes up to isomorphism with any equivalence of sheaf categories.

This is an auxiliary definition used to prove `Sheaf.isDiscrete_iff_of_equivalence` below, which
says that the property of a sheaf of being a discrete object is invariant under equivalence of
sheaf categories.
-/
noncomputable def equivCommuteConstant : let e : Sheaf J A ≌ Sheaf K A := sheafEquiv G J K A
    constantSheaf J A ⋙ e.functor ≅ constantSheaf K A :=
  let e : Sheaf J A ≌ Sheaf K A := sheafEquiv G J K A
  ((constantSheafAdj J A ht).comp e.toAdjunction).leftAdjointUniq
    (constantSheafAdj K A ht')

variable (A) in
/--
The constant sheaf functor commutes up to isomorphism with any equivalence of sheaf categories.

This is an auxiliary definition used to prove `Sheaf.isDiscrete_iff_of_equivalence` below, which
says that the property of a sheaf of being a discrete object is invariant under equivalence of
sheaf categories.
-/
noncomputable def equivCommuteConstant' : let e : Sheaf J A ≌ Sheaf K A := sheafEquiv G J K A
    constantSheaf J A ≅ constantSheaf K A ⋙ e.inverse :=
  let e : Sheaf J A ≌ Sheaf K A := sheafEquiv G J K A
  isoWhiskerLeft (constantSheaf J A) e.unitIso ≪≫
    isoWhiskerRight (equivCommuteConstant J A ht K G ht') e.inverse

/--
The property of a sheaf of being a discrete object is invariant under equivalence of sheaf
categories.
-/
-- TODO: Remove the assumptions `[(constantSheaf J A).Faithful] [(constantSheaf J A).Full]` by
-- proving the necessary lemmas about commuting the counit with the equivalences.
lemma isDiscrete_iff_of_equivalence (F : Sheaf K A)
    [(constantSheaf J A).Faithful] [(constantSheaf J A).Full] :
    let e : Sheaf J A ≌ Sheaf K A := sheafEquiv G J K A
    (e.inverse.obj F).IsDiscrete J ht ↔ IsDiscrete K ht' F := by
  intro e
  have := Functor.Faithful.of_iso (equivCommuteConstant J A ht K G ht')
  have := Functor.Full.of_iso (equivCommuteConstant J A ht K G ht')
  simp only [isDiscrete_iff_mem_essImage]
  constructor
  · intro ⟨Y, ⟨i⟩⟩
    exact ⟨_, ⟨(equivCommuteConstant J A ht K G ht').symm.app _ ≪≫
      e.functor.mapIso i ≪≫ e.counitIso.app _⟩⟩
  · intro ⟨Y, ⟨i⟩⟩
    exact ⟨_, ⟨(equivCommuteConstant' J A ht K G ht').app _ ≪≫ e.inverse.mapIso i⟩⟩

end Equivalence

end

section Forget

variable {B : Type*} [Category B] (U : A ⥤ B) [HasWeakSheafify J B]
  [J.PreservesSheafification U] [J.HasSheafCompose U] (F : Sheaf J A)

open Limits

/-- The constant sheaf functor commutes with `sheafCompose` up to isomorphism. -/
noncomputable def constantCommuteCompose :
    constantSheaf J A ⋙ sheafCompose J U ≅ U ⋙ constantSheaf J B :=
  (isoWhiskerLeft (const Cᵒᵖ)
    (sheafComposeNatIso J U (sheafificationAdjunction J A) (sheafificationAdjunction J B)).symm) ≪≫
      isoWhiskerRight (compConstIso _ _).symm _

lemma constantCommuteCompose_hom_app_val (X : A) : ((constantCommuteCompose J U).hom.app X).val =
    (sheafifyComposeIso J U ((const Cᵒᵖ).obj X)).inv ≫ sheafifyMap J (constComp Cᵒᵖ X U).hom := rfl

/-- The counit of `constantSheafAdj` factors through the isomorphism `constantCommuteCompose`. -/
lemma constantSheafAdj_counit_w :
    ((constantCommuteCompose J U).hom.app (F.val.obj ⟨t⟩)) ≫
      ((constantSheafAdj J B ht).counit.app ((sheafCompose J U).obj F)) =
        ((sheafCompose J U).map ((constantSheafAdj J A ht).counit.app F)) := by
  apply Sheaf.hom_ext
  rw [instCategorySheaf_comp_val, constantCommuteCompose_hom_app_val, assoc, Iso.inv_comp_eq]
  apply sheafify_hom_ext _ _ _ ((sheafCompose J U).obj F).cond
  ext
  simp? [constantSheafAdj_counit_app] says simp only [comp_obj, const_obj_obj, sheafCompose_obj_val,
      id_obj, constantSheafAdj_counit_app, evaluation_obj_obj, instCategorySheaf_comp_val,
      sheafificationAdjunction_counit_app_val, sheafifyMap_sheafifyLift, comp_id,
      toSheafify_sheafifyLift, NatTrans.comp_app, constComp_hom_app,
      constantPresheafAdj_counit_app_app, Functor.comp_map, id_comp, flip_obj_obj,
      sheafToPresheaf_obj, map_comp, sheafCompose_map_val, sheafComposeIso_hom_fac_assoc,
      whiskerRight_app]
  simp [← map_comp, ← NatTrans.comp_app]

lemma sheafCompose_reflects_discrete [(sheafCompose J U).ReflectsIsomorphisms]
    [((sheafCompose J U).obj F).IsDiscrete J ht] : F.IsDiscrete J ht := by
  have : IsIso ((sheafCompose J U).map ((constantSheafAdj J A ht).counit.app F)) := by
    rw [← constantSheafAdj_counit_w]
    infer_instance
  exact isIso_of_reflects_iso _ (sheafCompose J U)

instance [h : F.IsDiscrete J ht] : ((sheafCompose J U).obj F).IsDiscrete J ht := by
  have : IsIso ((sheafCompose J U).map ((constantSheafAdj J A ht).counit.app F)) := inferInstance
  rw [← constantSheafAdj_counit_w] at this
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance this

lemma isDiscrete_iff_forget [(sheafCompose J U).ReflectsIsomorphisms] : F.IsDiscrete J ht ↔
    ((sheafCompose J U).obj F).IsDiscrete J ht :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ sheafCompose_reflects_discrete _ _ U F⟩

end Forget

end CategoryTheory.Sheaf
