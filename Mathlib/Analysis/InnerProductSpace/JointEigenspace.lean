/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jack Cheverton, Samyak Dhar Tuladhar
-/

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Order.CompleteLattice
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Joint eigenspaces of commuting symmetric operators

This file collects various decomposition results for joint eigenspaces of commuting
symmetric operators on a finite-dimensional inner product space.

# Main Result

* `LinearMap.IsSymmetric.directSum_isInternal_of_commute` establishes that
   if `{A B : E →ₗ[𝕜] E}`, then `IsSymmetric A`, `IsSymmetric B` and `A ∘ₗ B = B ∘ₗ A` imply that
   `E` decomposes as an internal direct sum of the pairwise orthogonal spaces
   `eigenspace B μ ⊓ eigenspace A ν`
* `LinearMap.IsSymmetric.directSum_isInternal_of_commute_of_fintype` establishes the
   analogous result to `LinearMap.IsSymmetric.directSum_isInternal_of_commute` for finite commuting
   tuples of symmetric operators.

## TODO

Develop a `Diagonalization` structure for linear maps and / or matrices which consists of a basis,
and a proof obligation that the basis vectors are eigenvectors.

## Tags

symmetric operator, simultaneous eigenspaces, joint eigenspaces

-/

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open Module.End

namespace LinearMap

namespace IsSymmetric

section Pair

variable {α : 𝕜} {A B : E →ₗ[𝕜] E}

/-- If a pair of operators commute, then the eigenspaces of one are invariant under the other. -/
theorem eigenspace_invariant_of_commute
    (hAB : A ∘ₗ B = B ∘ₗ A) (α : 𝕜) : ∀ v ∈ (eigenspace A α), (B v ∈ eigenspace A α) := by
  intro v hv
  rw [eigenspace, mem_ker, sub_apply, Module.algebraMap_end_apply, ← comp_apply A B v, hAB,
    comp_apply B A v, ← map_smul, ← map_sub, hv, map_zero] at *

/-- The simultaneous eigenspaces of a pair of commuting symmetric operators form an
`OrthogonalFamily`. -/
theorem orthogonalFamily_eigenspace_inf_eigenspace (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun (i : 𝕜 × 𝕜) => (eigenspace A i.2 ⊓ eigenspace B i.1 : Submodule 𝕜 E))
    (fun i => (eigenspace A i.2 ⊓ eigenspace B i.1).subtypeₗᵢ) :=
     OrthogonalFamily.of_pairwise fun i j hij v ⟨hv1 , hv2⟩ ↦ by
    obtain (h₁ | h₂) : i.1 ≠ j.1 ∨ i.2 ≠ j.2 := by rwa [Ne.eq_def, Prod.ext_iff, not_and_or] at hij
    all_goals intro w ⟨hw1, hw2⟩
    · exact hB.orthogonalFamily_eigenspaces.pairwise h₁ hv2 w hw2
    · exact hA.orthogonalFamily_eigenspaces.pairwise h₂ hv1 w hw1

open Submodule in

/-- The intersection of eigenspaces of commuting selfadjoint operators is equal to the eigenspace of
one operator restricted to the eigenspace of the other, which is an invariant subspace because the
operators commute. -/
theorem eigenspace_inf_eigenspace
    (hAB : A ∘ₗ B = B ∘ₗ A) (γ : 𝕜) :
    eigenspace A α ⊓ eigenspace B γ = map (Submodule.subtype (eigenspace A α))
      (eigenspace (B.restrict (eigenspace_invariant_of_commute hAB α)) γ) :=
  (eigenspace A α).inf_genEigenspace _ _ (k := 1)

variable [FiniteDimensional 𝕜 E]

/-- If A and B are commuting symmetric operators on a finite dimensional inner product space
then the eigenspaces of the restriction of B to any eigenspace of A exhaust that eigenspace. -/
theorem iSup_eigenspace_inf_eigenspace (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A):
    (⨆ γ, eigenspace A α ⊓ eigenspace B γ) = eigenspace A α := by
  conv_rhs => rw [← (eigenspace A α).map_subtype_top]
  simp only [eigenspace_inf_eigenspace hAB, ← Submodule.map_iSup]
  congr 1
  rw [← Submodule.orthogonal_eq_bot_iff]
  exact orthogonalComplement_iSup_eigenspaces_eq_bot <|
    hB.restrict_invariant <| eigenspace_invariant_of_commute hAB α

/-- If A and B are commuting symmetric operators acting on a finite dimensional inner product space,
then the simultaneous eigenspaces of A and B exhaust the space. -/
theorem iSup_iSup_eigenspace_inf_eigenspace_eq_top (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A) :
    (⨆ α, ⨆ γ, eigenspace A α ⊓ eigenspace B γ) = ⊤ := by
  simpa [iSup_eigenspace_inf_eigenspace hB hAB] using
    Submodule.orthogonal_eq_bot_iff.mp <| hA.orthogonalComplement_iSup_eigenspaces_eq_bot

/-- Given a commuting pair of symmetric linear operators on a finite dimensional inner product
space, the space decomposes as an internal direct sum of simultaneous eigenspaces of these
operators. -/
theorem directSum_isInternal_of_commute (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAB : A ∘ₗ B = B ∘ₗ A) :
    DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) ↦ (eigenspace A i.2 ⊓ eigenspace B i.1)):= by
  apply (orthogonalFamily_eigenspace_inf_eigenspace hA hB).isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff, iSup_prod, iSup_comm]
  exact iSup_iSup_eigenspace_inf_eigenspace_eq_top hA hB hAB

end Pair

section Tuple

universe u

variable {n m : Type u}

open Submodule

/-- The indexed infimum of eigenspaces of a commuting family of linear operators is
invariant under each operator. -/
theorem iInf_eigenspace_invariant_of_commute {T : n → E →ₗ[𝕜] E}
    (hC : ∀ i j, T i ∘ₗ T j = T j ∘ₗ T i) (i : n) (γ : {x // x ≠ i} → 𝕜) (v : E)
    (hv : v ∈ ⨅ j, eigenspace (Subtype.restrict (· ≠ i) T j) (γ j)) :
    T i v ∈ ⨅ j, eigenspace (Subtype.restrict (· ≠ i) T j) (γ j) := by
  simp only [mem_iInf] at hv ⊢
  exact fun j ↦ eigenspace_invariant_of_commute (hC j i) (γ j) v (hv j)

/-- If `F` is an invariant subspace of a symmetric operator `S`, then `F` is the supremum of the
eigenspaces of the restriction of `S` to `F`. -/
theorem iSup_eigenspace_restrict [FiniteDimensional 𝕜 E] {F : Submodule 𝕜 E}
    (S : E →ₗ[𝕜] E) (hS : IsSymmetric S) (hInv : ∀ v ∈ F, S v ∈ F) :
    ⨆ μ, map F.subtype (eigenspace (S.restrict hInv) μ) = F := by
  conv_lhs => rw [← Submodule.map_iSup]
  conv_rhs => rw [← map_subtype_top F]
  congr!
  have H : IsSymmetric (S.restrict hInv) := fun x y ↦ hS (F.subtype x) y
  apply orthogonal_eq_bot_iff.mp (H.orthogonalComplement_iSup_eigenspaces_eq_bot)

open Classical

@[simp]
theorem Module.End.genEigenspace_one {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f : Module.End R M) (μ : R) : (f.genEigenspace μ) 1 = f.eigenspace μ :=
  rfl

/-- The orthocomplement of the indexed supremum of joint eigenspaces of a finite commuting tuple of
symmetric operators is trivial. -/
theorem orthogonalComplement_iSup_iInf_eigenspaces_eq_bot [Fintype n] [FiniteDimensional 𝕜 E]
    (T : n → (E →ₗ[𝕜] E)) (hT :(∀ (i : n), ((T i).IsSymmetric)))
    (hC : (∀ (i j : n), (T i) ∘ₗ (T j) = (T j) ∘ₗ (T i))) :
    (⨆ (γ : n → 𝕜), (⨅ (j : n), (eigenspace (T j) (γ j)) : Submodule 𝕜 E))ᗮ = ⊥ := by
  revert T
  refine Fintype.induction_subsingleton_or_nontrivial n (fun m _ hhm T hT _ ↦ ?_)
    (fun m hm hmm H T hT hC ↦ ?_)
  · obtain (hm | hm) := isEmpty_or_nonempty m
    · simp
    · have := uniqueOfSubsingleton (choice hm)
      simpa only [ciInf_unique, ← (Equiv.funUnique m 𝕜).symm.iSup_comp]
        using hT default |>.orthogonalComplement_iSup_eigenspaces_eq_bot
  · have i := Classical.arbitrary m
    specialize H {x // x ≠ i} (Fintype.card_subtype_lt (x := i) (by simp))
      (Subtype.restrict (· ≠ i) T) (hT ·) (hC · ·)
    simp only [Submodule.orthogonal_eq_bot_iff] at *
    rw [← (Equiv.funSplitAt i 𝕜).symm.iSup_comp, iSup_prod, iSup_comm]
    convert H with γ
    rw [← iSup_eigenspace_restrict (T i) (hT i) (iInf_eigenspace_invariant_of_commute hC i γ)]
    congr! with μ
    rw [← Module.End.genEigenspace_one, ← Submodule.inf_genEigenspace _ _ _ (k := 1), inf_comm,
      iInf_split_single _ i, iInf_subtype]
    congr! with x hx
    · simp
    · simp [dif_neg hx]

end Tuple

end IsSymmetric

end LinearMap
