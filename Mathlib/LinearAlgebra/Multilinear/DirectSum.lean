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

private theorem fromDirectSum_aux1 (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) {p : Π i, κ i}
    (hp : p ∉ Fintype.piFinset (fun i ↦ (x i).support)) :
    (f p) (fun j ↦ (x j) (p j)) = 0 := by
  simp only [Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq, not_forall, not_not] at hp
  obtain ⟨i, hi⟩ := hp
  exact (f p).map_coord_zero i hi

omit [Fintype ι] [(i : ι) → DecidableEq (κ i)]
  [(i : ι) → (j : κ i) → (x : M i j) → Decidable (x ≠ 0)] in
private theorem fromDirectSum_aux2 (x : Π i, ⨁ (j : κ i), M i j) (i : ι) (p : Π i, κ i)
    (a : ⨁ (j : κ i), M i j) :
    (fun j ↦ (update x i a j) (p j)) = update (fun j ↦ x j (p j)) i (a (p i)) := by
  ext j
  by_cases h : j = i
  · rw [h]; simp only [update_same]
  · simp only [ne_eq, h, not_false_eq_true, update_noteq]

/-- Given a family indexed by `p : Π i : ι, κ i` of multilinear maps on the
`fun i ↦ M i (p i)`, construct a multilinear map on `fun i ↦ ⨁ j : κ i, M i j`.-/
def fromDirectSum (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M') :
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' :=
  (DirectSum.toModule _ _ _ fun _ => .id).compMultilinearMap <| DFinsupp.piMultilinear f

theorem fromDirectSum_apply (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) :
    fromDirectSum R κ f x =
      ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := by
  classical
  refine (DFinsupp.sumAddHom_apply _ _).trans ?_
  change Finset.sum _ _ = _
  refine Finset.sum_subset (DFinsupp.support_piMultilinear_subset _ _) ?_
  simp

/-- The construction `MultilinearMap.fromDirectSum`, as an `R`-linear map.-/
def fromDirectSumₗ : ((p : Π i, κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') →ₗ[R]
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' where
  toFun := fromDirectSum R κ
  map_add' f g := by simp [fromDirectSum]
  map_smul' c f := by
    ext x
    simp only [fromDirectSum_apply, Pi.smul_apply, MultilinearMap.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]

@[simp]
theorem fromDirectSumₗ_apply (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) :
    fromDirectSumₗ R κ f x =
      ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) :=
  rfl

theorem _root_.piFinset_support_lof_sub (p : Π i, κ i) (a : Π i, M i (p i)) :
    Fintype.piFinset (fun i ↦ DFinsupp.support (lof R (κ i) (M i) (p i) (a i))) ⊆ {p} := by
  intro q
  simp only [Fintype.mem_piFinset, ne_eq, Finset.mem_singleton]
  simp_rw [DirectSum.lof_eq_of]
  exact fun hq ↦ funext fun i ↦ Finset.mem_singleton.mp (DirectSum.support_of_subset (hq i))

/-- Two multilinear maps from direct sums are equal if they agree on the generators. -/
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

/-- The linear equivalence between families indexed by `p : Π i : ι, κ i` of multilinear maps
on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ ⨁ j : κ i, M i j`.-/
def fromDirectSumEquiv :
    ((p : Π i, κ i) → MultilinearMap R (fun i ↦ M i (p i)) M') ≃ₗ[R]
    MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M' :=
  LinearEquiv.ofLinear
    (fromDirectSumₗ R κ)
    (LinearMap.pi (fun p ↦ MultilinearMap.compLinearMapₗ (fun i ↦ DirectSum.lof R (κ i) _ (p i))))
    (by
      ext f x
      simp only [coe_comp, Function.comp_apply, fromDirectSumₗ_apply, pi_apply,
        MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply, id_coe, id_eq]
      change _ = f (fun i ↦ x i)
      nth_rewrite 3 [funext (fun i ↦ Eq.symm (DirectSum.sum_support_of (x i)))]
      rw [MultilinearMap.map_sum_finset]
      rfl)
    (by
      ext f p a
      simp only [coe_comp, Function.comp_apply, LinearMap.pi_apply, compLinearMapₗ_apply,
        compLinearMap_apply, fromDirectSumₗ_apply, id_coe, id_eq]
      rw [Finset.sum_subset (piFinset_support_lof_sub R κ p a)]
      · rw [Finset.sum_singleton]
        simp only [lof_apply]
      · simp only [Finset.mem_singleton, Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq,
          not_forall, not_not, forall_exists_index, forall_eq, lof_apply]
        intro i hi
        exact (f p).map_coord_zero i hi)

@[simp]
theorem fromDirectSumEquiv_apply (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) M')
    (x : Π i, ⨁ (j : κ i), M i j) :
    fromDirectSumEquiv R κ f x =
      ∑ p in Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) :=
  rfl

@[simp]
theorem fromDirectSumEquiv_symm_apply (f : MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M')
    (p : Π i, κ i) :
    (fromDirectSumEquiv R κ).symm f p = f.compLinearMap (fun i ↦ DirectSum.lof R (κ i) _ (p i)) :=
  rfl

end MultilinearMap
