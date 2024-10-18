/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.DFinsupp.Multilinear

/-!
# Multilinear maps from direct sums

This file describes multilinear maps on direct sums.

## Main results

* `MultilinearMap.fromDirectSumEquiv` : If 'ι` is a `Fintype`, `κ i` is a family of types
indexed by `ι` and we are given a `R`-module `M i j` for every `i : ι` and `j : κ i`, this is
the linear equivalence between `Π p : (i : ι) → κ i, MultilinearMap R (fun i ↦ M i (p i)) M'` and
`MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M'`.
-/

namespace MultilinearMap

open DirectSum LinearMap Function

variable (R : Type*) [CommSemiring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (κ : ι → Type*) [(i : ι) → DecidableEq (κ i)]
variable {M : (i : ι) → κ i → Type*} {M' : Type*}
variable [Π i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']
variable [Π i (j : κ i), Module R (M i j)] [Module R M']
variable [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]

/-- Two multilinear maps from direct sums are equal if they agree on the generators. -/
@[ext]
theorem ext_directSum ⦃f g : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M'⦄
    (h : ∀ p : Π i, κ i,
      f.compLinearMap (fun i => DirectSum.lof R _ _ (p i)) =
      g.compLinearMap (fun i => DirectSum.lof R _ _ (p i))) : f = g := by
  ext x
  show f (fun i ↦ x i) = g (fun i ↦ x i)
  rw [funext (fun i ↦ Eq.symm (DirectSum.sum_support_of (x i)))]
  simp_rw [MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

omit [(i : ι) → (j : κ i) → (x : M i j) → Decidable (x ≠ 0)] in
/-- Two multilinear maps from finite products are equal if they agree on the generators. -/
@[ext]
theorem ext_pi [∀ i, Finite (κ i)] ⦃f g : MultilinearMap R (fun i ↦ Π j : κ i, M i j) M'⦄
    (h : ∀ p : Π i, κ i,
      f.compLinearMap (fun i => LinearMap.single R _ (p i)) =
      g.compLinearMap (fun i => LinearMap.single R _ (p i))) : f = g := by
  ext x
  have := fun i => (nonempty_fintype (κ i)).some
  show f (fun i ↦ x i) = g (fun i ↦ x i)
  rw [funext (fun i ↦ Eq.symm (Finset.univ_sum_single (x i)))]
  simp_rw [MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

/-- The linear equivalence between families indexed by `p : Π i : ι, κ i` of multilinear maps
on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ ⨁ j : κ i, M i j`.-/
def fromDirectSumEquiv :
    ((p : Π i, κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') ≃ₗ[R]
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' :=
  LinearEquiv.ofLinear
    ((DirectSum.toModule _ _ _ fun _ => .id).compMultilinearMapₗ ∘ₗ DFinsupp.piMultilinearₗ)
    (LinearMap.pi fun p ↦ MultilinearMap.compLinearMapₗ fun i ↦ DirectSum.lof R (κ i) _ (p i))
    (by
      ext f x
      dsimp
      erw [DFinsupp.piMultilinear_single, DirectSum.toModule_lof]
      rfl)
    (by
      ext f p a
      dsimp
      erw [DFinsupp.piMultilinear_single, DirectSum.toModule_lof]
      rfl)

theorem fromDirectSumEquiv_apply (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) :
    fromDirectSumEquiv R κ f x =
      ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := by
  classical
  refine (DFinsupp.sumAddHom_apply _ _).trans ?_
  refine Finset.sum_subset (DFinsupp.support_piMultilinear_subset _ _) ?_
  simp

@[simp]
theorem fromDirectSumEquiv_symm_apply (f : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M')
    (p : Π i, κ i) :
    (fromDirectSumEquiv R κ).symm f p = f.compLinearMap (fun i ↦ DirectSum.lof R (κ i) _ (p i)) :=
  rfl

end MultilinearMap
