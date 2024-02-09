/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.Algebra.Category.FGModuleCat.Kernels
import Mathlib.RingTheory.Noetherian
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The category of finitely generated modules over a Noetherian ring is abelian.

This file is basically a copy of `Algebra/ModuleCat/Abelian.lean`
-/

open CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

namespace FGModuleCat

variable {M N : FGModuleCat R} (f : M ⟶ N)

noncomputable def normalMono (hf : Mono f) : NormalMono f where
  Z := of R (N ⧸ LinearMap.range f)
  g := f.range.mkQ
  w := LinearMap.range_mkQ_comp _
  isLimit :=
    IsKernel.isoKernel _ _ (kernelIsLimit _)
      (LinearEquiv.toFGModuleCatIso
        ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
          (LinearMap.quotKerEquivRange f ≪≫ₗ
          LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm))) <| by ext; rfl

noncomputable def normalEpi (hf : Epi f) : NormalEpi f where
  W := of R (LinearMap.ker f)
  g := (LinearMap.ker f).subtype
  w := LinearMap.comp_ker_subtype _
  isColimit :=
    letI : Module.Finite R N.obj := N.2
    IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
      (LinearEquiv.toFGModuleCatIso
        (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ
            LinearMap.quotKerEquivRange f ≪≫ₗ
          LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <| by ext; rfl

noncomputable instance : Abelian (FGModuleCat R) where
  normalMonoOfMono := normalMono
  normalEpiOfEpi := normalEpi
  has_cokernels := hasCokernels_fgModuleCat

end FGModuleCat
