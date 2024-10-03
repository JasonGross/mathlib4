/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Discrete.Colimit
import Mathlib.Condensed.Discrete.Module
/-!

# Characterizing discrete condensed sets.

This file proves a characterization of discrete condensed sets and discrete light condensed sets,
see `CondensedSet.isDiscrete_tfae` and `LightCondSet.isDiscrete_tfae`.
-/

universe u

open CategoryTheory Limits Functor FintypeCat

attribute [local instance] ConcreteCategory.instFunLike

namespace Condensed

variable {C : Type*} [Category C] [HasWeakSheafify (coherentTopology CompHaus.{u}) C]

/--
A condensed object is *discrete* if it is constant as a sheaf, i.e. isomorphic to a constant sheaf.
-/
abbrev IsDiscrete (X : Condensed.{u} C) := X.IsConstant (coherentTopology CompHaus)

end Condensed

namespace CondensedSet

/--
This is an auxiliary definition to prove that the constant sheaf functor from `Type (u+1)`
to sheaves for the coherent topology on `Profinite.{u}` is fully faithful.
-/
noncomputable
def constantSheafProfiniteCompHausIso : constantSheaf (coherentTopology Profinite) (Type (u+1)) ≅
    constantSheaf (coherentTopology CompHaus) (Type (u+1)) ⋙
    (Condensed.ProfiniteCompHaus.equivalence _).inverse :=
  (equivCommuteConstant' (coherentTopology Profinite) (Type (u+1))
    (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
     CompHaus.isTerminalPUnit)

instance : (constantSheaf (coherentTopology Profinite) (Type (u+1))).Faithful :=
  Functor.Faithful.of_iso constantSheafProfiniteCompHausIso.symm

instance : (constantSheaf (coherentTopology Profinite) (Type (u+1))).Full :=
  Functor.Full.of_iso constantSheafProfiniteCompHausIso.symm

open CompHausLike.LocallyConstant

lemma mem_locallyContant_essImage_of_isColimit_mapCocone (X : CondensedSet.{u})
    (h : ∀ S : Profinite.{u}, IsColimit <|
      (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op) :
    X ∈ CondensedSet.LocallyConstant.functor.essImage := by
  let e : CondensedSet.{u} ≌ Sheaf (coherentTopology Profinite) _ :=
    (Condensed.ProfiniteCompHaus.equivalence (Type (u + 1))).symm
  let i : (e.functor.obj X).val ≅ (e.functor.obj (LocallyConstant.functor.obj _)).val :=
    Condensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨e.functor.preimageIso ((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

/--
`CondensedSet.LocallyConstant.functor` is left adjoint to the forgetful functor from light condensed
sets to sets.
-/
noncomputable abbrev LocallyConstant.adjunction :
    CondensedSet.LocallyConstant.functor ⊣ Condensed.underlying (Type (u+1)) :=
  CompHausLike.LocallyConstant.adjunction _ _

noncomputable instance : PreservesFiniteCoproducts profiniteToCompHaus :=
  inferInstanceAs (PreservesFiniteCoproducts (CompHausLike.toCompHausLike _))

noncomputable instance : PreservesFiniteProducts profiniteToCompHaus.op :=
  inferInstanceAs (PreservesFiniteProducts (CompHausLike.toCompHausLike _).op)

open Condensed

open CondensedSet.LocallyConstant List in
theorem isDiscrete_tfae  (X : CondensedSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , IsIso ((Condensed.discreteUnderlyingAdj _).counit.app X)
    , X ∈ (Condensed.discrete _).essImage
    , X ∈ functor.essImage
    , IsIso (adjunction.counit.app X)
    , Sheaf.IsConstant (coherentTopology Profinite)
        ((Condensed.ProfiniteCompHaus.equivalence _).inverse.obj X)
    , ∀ S : Profinite.{u}, Nonempty
        (IsColimit <| (profiniteToCompHaus.op ⋙ X.val).mapCocone S.asLimitCone.op)
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ CompHaus.isTerminalPUnit adjunction _
  tfae_have 1 ↔ 6 :=
    (Sheaf.isConstant_iff_of_equivalence (coherentTopology Profinite)
      (coherentTopology CompHaus) profiniteToCompHaus Profinite.isTerminalPUnit
      CompHaus.isTerminalPUnit _).symm
  tfae_have 7 → 4 := fun h ↦
    mem_locallyContant_essImage_of_isColimit_mapCocone X (fun S ↦ (h S).some)
  tfae_have 4 → 7 := fun ⟨Y, ⟨i⟩⟩ S ↦
    ⟨IsColimit.mapCoconeEquiv (isoWhiskerLeft profiniteToCompHaus.op
      ((sheafToPresheaf _ _).mapIso i))
      (Condensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end CondensedSet

namespace CondensedMod

variable (R : Type (u+1)) [Ring R]

lemma isDiscrete_iff_isDiscrete_forget (M : CondensedMod R) :
    M.IsDiscrete ↔ ((Condensed.forget R).obj M).IsDiscrete  :=
  Sheaf.isConstant_iff_forget (coherentTopology CompHaus)
    (CategoryTheory.forget (ModuleCat R)) M CompHaus.isTerminalPUnit

end CondensedMod

namespace LightCondensed

variable {C : Type*} [Category C] [HasWeakSheafify (coherentTopology LightProfinite.{u}) C]

/--
A light condensed object is *discrete* if it is constant as a sheaf, i.e. isomorphic to a constant
sheaf.
-/
abbrev IsDiscrete (X : LightCondensed.{u} C) := X.IsConstant (coherentTopology LightProfinite)

end LightCondensed

namespace LightCondSet

instance : (constantSheaf (coherentTopology LightProfinite) (Type u)).Faithful :=
  inferInstanceAs (LightCondensed.discrete _).Faithful

instance : (constantSheaf (coherentTopology LightProfinite) (Type u)).Full :=
  inferInstanceAs (LightCondensed.discrete _).Full

lemma mem_locallyContant_essImage_of_isColimit_mapCocone (X : LightCondSet.{u})
    (h : ∀ S : LightProfinite.{u}, IsColimit <|
      X.val.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    X ∈ LightCondSet.LocallyConstant.functor.essImage := by
  let i : X.val ≅ (LightCondSet.LocallyConstant.functor.obj _).val :=
    LightCondensed.isoLocallyConstantOfIsColimit _ h
  exact ⟨_, ⟨((sheafToPresheaf _ _).preimageIso i.symm)⟩⟩

/--
`LightCondSet.LocallyConstant.functor` is left adjoint to the forgetful functor from light condensed
sets to sets.
-/
noncomputable abbrev LocallyConstant.adjunction :
    LightCondSet.LocallyConstant.functor ⊣ LightCondensed.underlying (Type u) :=
  CompHausLike.LocallyConstant.adjunction _ _

open LightCondSet.LocallyConstant List in
theorem isDiscrete_tfae  (X : LightCondSet.{u}) :
    TFAE
    [ X.IsDiscrete
    , IsIso ((LightCondensed.discreteUnderlyingAdj _).counit.app X)
    , X ∈ (LightCondensed.discrete _).essImage
    , X ∈ functor.essImage
    , IsIso (adjunction.counit.app X)
    , ∀ S : LightProfinite.{u}, Nonempty
        (IsColimit <| X.val.mapCocone (coconeRightOpOfCone S.asLimitCone))
    ] := by
  tfae_have 1 ↔ 2 := Sheaf.isConstant_iff_isIso_counit_app _ _ _
  tfae_have 1 ↔ 3 := ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩
  tfae_have 1 ↔ 4 := Sheaf.isConstant_iff_mem_essImage _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 1 ↔ 5 :=
    have : functor.Faithful := inferInstance
    have : functor.Full := inferInstance
    -- These `have` statements above shouldn't be needed, but they are.
    Sheaf.isConstant_iff_isIso_counit_app' _ LightProfinite.isTerminalPUnit adjunction X
  tfae_have 6 → 4 := fun h ↦
    mem_locallyContant_essImage_of_isColimit_mapCocone X (fun S ↦ (h S).some)
  tfae_have 4 → 6 := fun ⟨Y, ⟨i⟩⟩ S ↦
    ⟨IsColimit.mapCoconeEquiv ((sheafToPresheaf _ _).mapIso i)
      (LightCondensed.isColimitLocallyConstantPresheafDiagram Y S)⟩
  tfae_finish

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R]

lemma isDiscrete_iff_isDiscrete_forget (M : LightCondMod R) :
    M.IsDiscrete ↔ ((LightCondensed.forget R).obj M).IsDiscrete  :=
  Sheaf.isConstant_iff_forget (coherentTopology LightProfinite)
    (CategoryTheory.forget (ModuleCat R)) M LightProfinite.isTerminalPUnit

end LightCondMod
