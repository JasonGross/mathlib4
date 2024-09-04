/-
Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, María Inés de Frutos-Fernández
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# The adele ring of a number field

This file contains the formalisation of the infinite adele ring of a number field as the
finite product of completions over its infinite places and the adele ring of a number field as the
direct product of the infinite adele ring and the finite adele ring.

## Main definitions
 - `NumberField.InfiniteAdeleRing` of a number field `K` is defined as the product of
   the completions of `K` over its Archimedean places.
 - `NumberField.InfiniteAdeleRing.equiv_mixedSpace` is the ring isomorphism between
   the infinite adele ring of `K` and `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature
   of `K`.
 - `NumberField.AdeleRing K` is the adele ring of a number field `K`.
 - `NumberField.AdeleRing.globalEmbedding K` is the map sending `x ∈ K` to `(x)ᵥ`.
 - `NumberField.AdeleRing.principalSubgroup K` is the subgroup of principal adeles `(x)ᵥ`.

## Main results
 - `NumberField.InfiniteAdeleRing.locallyCompactSpace` : the infinite adele ring is a
   locally compact space.

## Tags
infinite adele ring, adele ring, number field
-/

noncomputable section

namespace NumberField

open InfinitePlace InfinitePlace.Completion AbsoluteValue.Completion DedekindDomain IsDedekindDomain


open scoped Classical

variable (K : Type*) [Field K] (v : InfinitePlace K)

/-- The infinite adele ring of a number field. -/
def InfiniteAdeleRing := (v : InfinitePlace K) → v.completion

namespace InfiniteAdeleRing

section DerivedInstances

instance : CommRing (InfiniteAdeleRing K) := Pi.commRing

instance : Inhabited (InfiniteAdeleRing K) := ⟨0⟩

instance [NumberField K] : Nontrivial (InfiniteAdeleRing K) :=
  (inferInstanceAs <| Nonempty (InfinitePlace K)).elim fun w => Pi.nontrivial_at w

end DerivedInstances

instance : TopologicalSpace (InfiniteAdeleRing K) := Pi.topologicalSpace

instance : TopologicalRing (InfiniteAdeleRing K) := Pi.instTopologicalRing

instance : Algebra K (InfiniteAdeleRing K) := Pi.algebra _ _

/-- The global embedding of a number field into its infinite adele ring,
sending `x ∈ K` to `(x)ᵥ`. -/
abbrev globalEmbedding : K →+* InfiniteAdeleRing K := algebraMap K (InfiniteAdeleRing K)

@[simp]
theorem globalEmbedding_apply (x : K) : globalEmbedding K x v = x := rfl

/-- The infinite adele ring is locally compact. -/
instance locallyCompactSpace [NumberField K] : LocallyCompactSpace (InfiniteAdeleRing K) :=
  Pi.locallyCompactSpace_of_finite

/-- The ring isomorphism between the infinite adele ring of a number field and the
space `ℝ ^ r₁ × ℂ ^ r₂`, where `(r₁, r₂)` is the signature of the number field. -/
abbrev equiv_mixedSpace :
    InfiniteAdeleRing K ≃+*
      ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ) :=
  RingEquiv.trans
    (RingEquiv.piEquivPiSubtypeProd (fun (v : InfinitePlace K) => IsReal v)
      (fun (v : InfinitePlace K) => v.completion))
    (RingEquiv.prodCongr
      (RingEquiv.piCongrRight (fun ⟨_, hv⟩ => Completion.equiv_real_of_isReal hv))
      (RingEquiv.trans
        (RingEquiv.piCongrRight (fun v => Completion.equiv_complex_of_isComplex
          ((not_isReal_iff_isComplex.1 v.2))))
        (RingEquiv.piCongrLeft (fun _ => ℂ) <|
          Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex))))

@[simp]
theorem equiv_mixedSpace_apply (x : InfiniteAdeleRing K) :
    equiv_mixedSpace K x =
      (fun (v : {w : InfinitePlace K // IsReal w}) => equiv_real_of_isReal v.2 (x v),
       fun (v : {w : InfinitePlace K // IsComplex w}) => equiv_complex_of_isComplex v.2 (x v)) := by
  simp only [equiv_mixedSpace, RingEquiv.piEquivPiSubtypeProd, RingEquiv.prodCongr,
    RingEquiv.piCongrLeft, RingEquiv.coe_trans, Equiv.prodCongr_apply, EquivLike.coe_coe,
    Function.comp_apply, Prod.map_apply, RingEquiv.piCongrRight, Equiv.piEquivPiSubtypeProd,
    RingEquiv.piCongrLeft', Equiv.piCongrLeft', RingEquiv.symm_mk, RingEquiv.coe_mk,
    Equiv.coe_fn_mk, Equiv.subtypeEquivRight_symm_apply_coe]

/-- Transfers the global embedding of `x ↦ (x)ᵥ` of the number field `K` into its infinite adele
ring to the mixed embedding `x ↦ (φᵢ(x))ᵢ` of `K` into the space `ℝ ^ r₁ × ℂ ^ r₂`, where
`(r₁, r₂)` is the signature of `K` and `φᵢ` are the complex embeddings of `K`. -/
theorem mixedEmbedding_eq_globalEmbedding_comp {x : K} :
    mixedEmbedding K x = equiv_mixedSpace K (algebraMap K _ x) := by
  ext ⟨v, hv⟩ <;> simp only [equiv_mixedSpace_apply, globalEmbedding_apply,
    equiv_real_of_isReal, equiv_complex_of_isComplex, extensionEmbedding,
    extensionEmbedding_of_isReal, extensionEmbedding_of_comp, RingEquiv.coe_ofBijective,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.extensionHom]
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| abs_of_isReal_eq_comp hv).uniformContinuous x]
    rfl
  · rw [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp <| abs_eq_comp v).uniformContinuous x]
    rfl

end InfiniteAdeleRing

variable [NumberField K]

/-- The adele ring of a number field. -/
def AdeleRing := InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K

namespace AdeleRing

section DerivedInstances

instance : CommRing (AdeleRing K) := Prod.instCommRing

instance : Inhabited (AdeleRing K) := ⟨0⟩

instance : TopologicalSpace (AdeleRing K) :=
  instTopologicalSpaceProd

instance : TopologicalRing (AdeleRing K) :=
  instTopologicalRingProd

instance : Algebra K (AdeleRing K) := Prod.algebra _ _ _

end DerivedInstances

/-- The global embedding sending `x ∈ K` to `(x)ᵥ ∈ 𝔸_K`. -/
def globalEmbedding : K →+* AdeleRing K := algebraMap K (AdeleRing K)

@[simp]
theorem globalEmbedding_fst_apply (x : K) : (globalEmbedding K x).1 v = x := rfl

@[simp]
theorem globalEmbedding_snd_apply (x : K) (v : HeightOneSpectrum (𝓞 K)) :
    (globalEmbedding K x).2 v = x := rfl

theorem globalEmbedding_injective : Function.Injective (globalEmbedding K) :=
  fun _ _ hxy => (InfiniteAdeleRing.globalEmbedding K).injective (Prod.ext_iff.1 hxy).1

/-- The subgroup of principal adeles `(x)ᵥ` where `x ∈ K`. -/
def principalSubgroup : AddSubgroup (AdeleRing K) := (globalEmbedding K).range.toAddSubgroup

end AdeleRing

end NumberField
