/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.SeparationQuotient

/-!
# The Fréchet-Riesz representation theorem

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`toDualMap`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element
`x` of the space to `fun y => ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `toDual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `toDualMap`.  This is the Fréchet-Riesz representation theorem: every element of
the dual of a Hilbert space `E` has the form `fun u => ⟪x, u⟫` for some `x : E`.

For a bounded sesquilinear form `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`,
we define a map `InnerProductSpace.continuousLinearMapOfBilin B : E →L[𝕜] E`,
given by substituting `E →L[𝕜] 𝕜` with `E` using `toDual`.


## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/

noncomputable section

open scoped Classical
open ComplexConjugate

universe u v

namespace InnerProductSpace

open RCLike ContinuousLinearMap

variable (𝕜 E : Type*)

section Seminormed

variable [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

local postfix:90 "†" => starRingEnd _

/-- An element `x` of an inner product space `E` induces an element of the dual space `Dual 𝕜 E`,
the map `fun y => ⟪x, y⟫`; moreover this operation is a conjugate-linear isometric embedding of `E`
into `Dual 𝕜 E`.
If `E` is complete, this operation is surjective, hence a conjugate-linear isometric equivalence;
see `toDual`.
-/
def toDualMap : E →ₗᵢ⋆[𝕜] NormedSpace.Dual 𝕜 E :=
  { innerSL 𝕜 with norm_map' := innerSL_apply_norm _ }

variable {E}

@[simp]
theorem toDualMap_apply {x y : E} : toDualMap 𝕜 E x y = ⟪x, y⟫ :=
  rfl

section NullSubmodule

open SeparationQuotientAddGroup LinearMap

variable (E)

/-- The null space with respect to the norm. -/
def nullSubmodule : Submodule 𝕜 E where
  __ := nullSubgroup
  smul_mem' c x (hx : ‖x‖ = 0) := show ‖c • x‖ = 0 from
    le_antisymm (norm_smul_le _ _ |>.trans <| by rw [hx, mul_zero]) (norm_nonneg _)

@[simp]
lemma mem_nullSubmodule_iff {x : E} : x ∈ nullSubmodule 𝕜 E ↔ ‖x‖ = 0 := Iff.rfl

lemma inner_eq_zero_of_left (x y : E) (h : ‖x‖ = 0) :
    ⟪x, y⟫_𝕜 = 0 := by
  rw [← norm_eq_zero, ← sq_eq_zero_iff]
  apply le_antisymm _ (sq_nonneg _)
  rw [sq]
  nth_rw 2 [← RCLike.norm_conj]
  rw [_root_.inner_conj_symm]
  calc ‖⟪x, y⟫_𝕜‖ * ‖⟪y, x⟫_𝕜‖ ≤ re ⟪x, x⟫_𝕜 * re ⟪y, y⟫_𝕜 := inner_mul_inner_self_le _ _
  _ = (‖x‖ * ‖x‖) * re ⟪y, y⟫_𝕜 := by rw [inner_self_eq_norm_mul_norm x]
  _ = (0 * 0) * re ⟪y, y⟫_𝕜 := by rw [(mem_nullSubmodule_iff 𝕜 E).mp h]
  _ = 0 := by ring

lemma inner_nullSubmodule_right_eq_zero (x y : E) (h : y ∈ nullSubmodule 𝕜 E) : ⟪x, y⟫_𝕜 = 0 := by
  rw [inner_eq_zero_symm]
  exact inner_eq_zero_of_left_mem_nullSubmodule 𝕜 E y x h

lemma norm_sub_eq_norm (x y : E) (h : y ∈ (nullSubmodule 𝕜 E)) : ‖x - y‖ = ‖x‖ := by
  rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), sq, sq,
    ← @inner_self_eq_norm_mul_norm 𝕜 E _ _ _ x, ← @inner_self_eq_norm_mul_norm 𝕜 E _ _ _ (x-y),
    inner_sub_sub_self, inner_nullSubmodule_right_eq_zero 𝕜 E x y h,
    inner_eq_zero_of_left_mem_nullSubmodule 𝕜 E y x h,
    inner_eq_zero_of_left_mem_nullSubmodule 𝕜 E y y h]
  simp only [sub_zero, add_zero]

/-- For each `x : E`, the kernel of `⟪x, ⬝⟫` includes the null space. -/
lemma nullSubmodule_le_ker_toDualMap (x : E) : nullSubmodule 𝕜 E ≤ ker (toDualMap 𝕜 E x) := by
  intro y hy
  refine LinearMap.mem_ker.mpr ?_
  simp only [toDualMap_apply]
  exact inner_nullSubmodule_right_eq_zero 𝕜 E x y hy

/-- The kernel of the map `x ↦ ⟪x, ⬝⟫` includes the null space. -/
lemma nullSubmodule_le_ker_toDualMap' : nullSubmodule 𝕜 E ≤ ker (toDualMap 𝕜 E) := by
  intro x hx
  refine LinearMap.mem_ker.mpr ?_
  ext y
  simp only [toDualMap_apply, ContinuousLinearMap.zero_apply]
  exact inner_eq_zero_of_left_mem_nullSubmodule 𝕜 E x y hx

lemma isClosed_nullSubmodule : IsClosed (nullSubmodule 𝕜 E : Set E) := isClosed_nullSubgroup

end NullSubmodule

end Seminormed

section Normed
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

local postfix:90 "†" => starRingEnd _

theorem innerSL_norm [Nontrivial E] : ‖(innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜)‖ = 1 :=
  show ‖(toDualMap 𝕜 E).toContinuousLinearMap‖ = 1 from LinearIsometry.norm_toContinuousLinearMap _

variable {E 𝕜}

theorem ext_inner_left_basis {ι : Type*} {x y : E} (b : Basis ι 𝕜 E)
    (h : ∀ i : ι, ⟪b i, x⟫ = ⟪b i, y⟫) : x = y := by
  apply (toDualMap 𝕜 E).map_eq_iff.mp
  refine (Function.Injective.eq_iff ContinuousLinearMap.coe_injective).mp (Basis.ext b ?_)
  intro i
  simp only [ContinuousLinearMap.coe_coe]
  rw [toDualMap_apply, toDualMap_apply]
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

theorem ext_inner_right_basis {ι : Type*} {x y : E} (b : Basis ι 𝕜 E)
    (h : ∀ i : ι, ⟪x, b i⟫ = ⟪y, b i⟫) : x = y := by
  refine ext_inner_left_basis b fun i => ?_
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

variable (𝕜) (E)
variable [CompleteSpace E]

/-- Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`fun u => ⟪y, u⟫` for some `y : E`, i.e. `toDualMap` is surjective.
-/
def toDual : E ≃ₗᵢ⋆[𝕜] NormedSpace.Dual 𝕜 E :=
  LinearIsometryEquiv.ofSurjective (toDualMap 𝕜 E)
    (by
      intro ℓ
      set Y := LinearMap.ker ℓ
      by_cases htriv : Y = ⊤
      · have hℓ : ℓ = 0 := by
          have h' := LinearMap.ker_eq_top.mp htriv
          rw [← coe_zero] at h'
          apply coe_injective
          exact h'
        exact ⟨0, by simp [hℓ]⟩
      · rw [← Submodule.orthogonal_eq_bot_iff] at htriv
        change Yᗮ ≠ ⊥ at htriv
        rw [Submodule.ne_bot_iff] at htriv
        obtain ⟨z : E, hz : z ∈ Yᗮ, z_ne_0 : z ≠ 0⟩ := htriv
        refine ⟨(starRingEnd (R := 𝕜) (ℓ z) / ⟪z, z⟫) • z, ?_⟩
        apply ContinuousLinearMap.ext
        intro x
        have h₁ : ℓ z • x - ℓ x • z ∈ Y := by
          rw [LinearMap.mem_ker, map_sub, ContinuousLinearMap.map_smul,
            ContinuousLinearMap.map_smul, Algebra.id.smul_eq_mul, Algebra.id.smul_eq_mul, mul_comm]
          exact sub_self (ℓ x * ℓ z)
        have h₂ : ℓ z * ⟪z, x⟫ = ℓ x * ⟪z, z⟫ :=
          haveI h₃ :=
            calc
              0 = ⟪z, ℓ z • x - ℓ x • z⟫ := by
                rw [(Y.mem_orthogonal' z).mp hz]
                exact h₁
              _ = ⟪z, ℓ z • x⟫ - ⟪z, ℓ x • z⟫ := by rw [inner_sub_right]
              _ = ℓ z * ⟪z, x⟫ - ℓ x * ⟪z, z⟫ := by simp [inner_smul_right]
          sub_eq_zero.mp (Eq.symm h₃)
        have h₄ :=
          calc
            ⟪(ℓ z† / ⟪z, z⟫) • z, x⟫ = ℓ z / ⟪z, z⟫ * ⟪z, x⟫ := by simp [inner_smul_left, conj_conj]
            _ = ℓ z * ⟪z, x⟫ / ⟪z, z⟫ := by rw [← div_mul_eq_mul_div]
            _ = ℓ x * ⟪z, z⟫ / ⟪z, z⟫ := by rw [h₂]
            _ = ℓ x := by field_simp [inner_self_ne_zero.2 z_ne_0]
        exact h₄)

variable {𝕜} {E}

@[simp]
theorem toDual_apply {x y : E} : toDual 𝕜 E x y = ⟪x, y⟫ :=
  rfl

@[simp]
theorem toDual_symm_apply {x : E} {y : NormedSpace.Dual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x := by
  rw [← toDual_apply]
  simp only [LinearIsometryEquiv.apply_symm_apply]

/-- Maps a bounded sesquilinear form to its continuous linear map,
given by interpreting the form as a map `B : E →L⋆[𝕜] NormedSpace.Dual 𝕜 E`
and dualizing the result using `toDual`.
-/
def continuousLinearMapOfBilin (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) : E →L[𝕜] E :=
  comp (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap B

local postfix:1024 "♯" => continuousLinearMapOfBilin

variable (B : E →L⋆[𝕜] E →L[𝕜] 𝕜)

@[simp]
theorem continuousLinearMapOfBilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w := by
  rw [continuousLinearMapOfBilin, coe_comp', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply, toDual_symm_apply]

theorem unique_continuousLinearMapOfBilin {v f : E} (is_lax_milgram : ∀ w, ⟪f, w⟫ = B v w) :
    f = B♯ v := by
  refine ext_inner_right 𝕜 ?_
  intro w
  rw [continuousLinearMapOfBilin_apply]
  exact is_lax_milgram w

end Normed

end InnerProductSpace
