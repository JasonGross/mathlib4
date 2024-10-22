/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Inner product space

This file defines inner product spaces and proves the basic properties.  We do not formally
define Hilbert spaces, but they can be obtained using the set of assumptions
`[NormedAddCommGroup E] [InnerProductSpace E] [CompleteSpace E]`.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `RCLike` typeclass.

This file proves general results on inner product spaces. For the specific construction of an inner
product structure on `n → ℂ` for `ℂ = ℝ` or `ℂ`, see `EuclideanSpace` in
`Analysis.InnerProductSpace.PiL2`.

## Main results

- We define the class `InnerProductSpace E` extending `NormedSpace ℂ E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `ℂ` is understood to be either `ℝ`
  or `ℂ`, through the `RCLike` typeclass.
- We show that the inner product is continuous, `continuous_inner`, and bundle it as the
  continuous sesquilinear map `innerSL` (see also `innerₛₗ` for the non-continuous version).
- We define `Orthonormal`, a predicate on a function `v : ι → E`, and prove the existence of a
  maximal orthonormal set, `exists_maximal_orthonormal`.  Bessel's inequality,
  `Orthonormal.tsum_inner_products_le`, states that given an orthonormal set `v` and a vector `x`,
  the sum of the norm-squares of the inner products `⟪v i, x⟫` is no more than the norm-square of
  `x`. For the existence of orthonormal bases, Hilbert bases, etc., see the file
  `Analysis.InnerProductSpace.projection`.

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫` respectively.
We also provide two notation namespaces: `RealInnerProductSpace`, `ComplexInnerProductSpace`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## Tags

inner product space, Hilbert space, norm

## References
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/


noncomputable section

open RCLike Real Filter

open Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {E F : Type*}

/-- Syntactic typeclass for types endowed with an inner product -/
class Inner (E : Type*) where
  /-- The inner product function. -/
  inner : E → E → ℂ

export Inner (inner)

/-- The inner product with values in `ℂ`. -/
scoped[InnerProductSpace] notation3:max "⟪" x ", " y "⟫" => @inner _ _ x y

/-- A (pre) inner product space is a vector space with an additional operation called inner product.
The (semi)norm could be derived from the inner product, instead we require the existence of a
seminorm and the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product spaces.

Note that `NormedSpace` does not assume that `‖x‖=0` implies `x=0` (it is rather a seminorm).

To construct a seminorm from an inner product, see `PreInnerProductSpace.ofCore`.
-/
class InnerProductSpace (E : Type*) [SeminormedAddCommGroup E] extends
  NormedSpace ℂ E, Inner E where
  /-- The inner product induces the norm. -/
  norm_sq_eq_inner : ∀ x : E, ‖x‖ ^ 2 = re (inner x x)
  /-- The inner product is *hermitian*, taking the `conj` swaps the arguments. -/
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`InnerProductSpace.Core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `InnerProductSpace`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `Core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/

/-- A structure requiring that a scalar product is positive semidefinite and symmetric. -/
structure PreInnerProductSpace.Core (F : Type*) [AddCommGroup F]
  [Module ℂ F] extends Inner F where
  /-- The inner product is *hermitian*, taking the `conj` swaps the arguments. -/
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is positive (semi)definite. -/
  nonneg_re : ∀ x, 0 ≤ re (inner x x)
  /-- The inner product is positive definite. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

attribute [class] PreInnerProductSpace.Core

/-- A structure requiring that a scalar product is positive definite. Some theorems that
require this assumptions are put under section `InnerProductSpace.Core`. -/
-- @[nolint HasNonemptyInstance] porting note: I don't think we have this linter anymore
structure InnerProductSpace.Core (F : Type*) [AddCommGroup F]
  [Module ℂ F] extends PreInnerProductSpace.Core F where
  /-- The inner product is positive definite. -/
  definite : ∀ x, inner x x = 0 → x = 0

/- We set `InnerProductSpace.Core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] InnerProductSpace.Core

instance (F : Type*) [AddCommGroup F]
  [Module ℂ F] [cd : InnerProductSpace.Core F] : PreInnerProductSpace.Core F where
  inner := cd.inner
  conj_symm := cd.conj_symm
  nonneg_re := cd.nonneg_re
  add_left := cd.add_left
  smul_left := cd.smul_left

/-- Define `PreInnerProductSpace.Core` from `PreInnerProductSpace`. Defined to reuse lemmas about
`PreInnerProductSpace.Core` for `PreInnerProductSpace`s. Note that the `Seminorm` instance provided
by `PreInnerProductSpace.Core.norm` is propositionally but not definitionally equal to the original
norm. -/
def PreInnerProductSpace.toCore [SeminormedAddCommGroup E] [c : InnerProductSpace E] :
    PreInnerProductSpace.Core E :=
  { c with
    nonneg_re := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_inner]
      apply sq_nonneg }

/-- Define `InnerProductSpace.Core` from `InnerProductSpace`. Defined to reuse lemmas about
`InnerProductSpace.Core` for `InnerProductSpace`s. Note that the `Norm` instance provided by
`InnerProductSpace.Core.norm` is propositionally but not definitionally equal to the original
norm. -/
def InnerProductSpace.toCore [NormedAddCommGroup E] [c : InnerProductSpace E] :
    InnerProductSpace.Core E :=
  { c with
    nonneg_re := fun x => by
      rw [← InnerProductSpace.norm_sq_eq_inner]
      apply sq_nonneg
    definite := fun x hx =>
      norm_eq_zero.1 <| pow_eq_zero (n := 2) <| by
        rw [InnerProductSpace.norm_sq_eq_inner x, hx, map_zero] }

namespace InnerProductSpace.Core

section PreInnerProductSpace.Core

variable [AddCommGroup F] [Module ℂ F] [c : PreInnerProductSpace.Core F]

local notation "⟪" x ", " y "⟫" => @Inner F _ x y

local notation "normSqK" => @RCLike.normSq ℂ _

local notation "reK" => @RCLike.re ℂ _

local notation "ext_iff" => @RCLike.ext_iff ℂ _

local postfix:90 "†" => starRingEnd _

/-- Inner product defined by the `PreInnerProductSpace.Core` structure. We can't reuse
`PreInnerProductSpace.Core.toInner` because it takes `PreInnerProductSpace.Core` as an explicit
argument. -/
def toPreInner' : Inner F :=
  c.toInner

attribute [local instance] toPreInner'

/-- The norm squared function for `PreInnerProductSpace.Core` structure. -/
def normSq (x : F) :=
  reK ⟪x, x⟫

local notation "normSqF" => @normSq F _ _ _

theorem inner_conj_symm (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  c.conj_symm x y

theorem inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ :=
  c.nonneg_re _

theorem inner_self_im (x : F) : im ⟪x, x⟫ = 0 := by
  rw [← @ofReal_inj ℂ, im_eq_conj_sub]
  simp [inner_conj_symm]

theorem inner_add_left (x y z : F) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  c.add_left _ _ _

theorem inner_add_right (x y z : F) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add]; simp only [inner_conj_symm]

theorem ofReal_normSq_eq_inner_self (x : F) : (normSqF x : ℂ) = ⟪x, x⟫ := by
  rw [ext_iff]
  sorry
  -- exact ⟨by simp only [ofReal_re]; rfl, by simp only [inner_self_im, ofReal_im]⟩

theorem inner_re_symm (x y : F) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

theorem inner_im_symm (x y : F) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

theorem inner_smul_left (x y : F) {r : ℂ} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  c.smul_left _ _ _

theorem inner_smul_right (x y : F) {r : ℂ} : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left]
  simp only [conj_conj, inner_conj_symm, RingHom.map_mul]

theorem inner_zero_left (x : F) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul ℂ (0 : F), inner_smul_left]
  simp only [zero_mul, RingHom.map_zero]

theorem inner_zero_right (x : F) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left]; simp only [RingHom.map_zero]

theorem inner_self_of_eq_zero {x : F} : x = 0 → ⟪x, x⟫ = 0 := by
  rintro rfl
  exact inner_zero_left _

theorem normSq_eq_zero_of_eq_zero {x : F} : x = 0 → normSqF x = 0 := by
  rintro rfl
  simp [normSq, inner_self_of_eq_zero]

theorem ne_zero_of_inner_self_ne_zero {x : F} : ⟪x, x⟫ ≠ 0 → x ≠ 0 :=
  mt inner_self_of_eq_zero
theorem inner_self_ofReal_re (x : F) : (re ⟪x, x⟫ : ℂ) = ⟪x, x⟫ := by
  norm_num [ext_iff, inner_self_im]
  sorry

theorem norm_inner_symm (x y : F) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]

theorem inner_neg_left (x y : F) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul ℂ x, inner_smul_left]
  simp

theorem inner_neg_right (x y : F) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left]; simp only [RingHom.map_neg, inner_conj_symm]

theorem inner_sub_left (x y z : F) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left, inner_neg_left]

theorem inner_sub_right (x y z : F) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right, inner_neg_right]

theorem inner_mul_symm_re_eq_norm (x y : F) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]
  exact re_eq_norm_of_mul_conj (inner y x)

/-- Expand `inner (x + y) (x + y)` -/
theorem inner_add_add_self (x y : F) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

-- Expand `inner (x - y) (x - y)`
theorem inner_sub_sub_self (x y : F) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring

theorem inner_smul_ofReal_left (x y : F) {t : ℝ} : ⟪(t : ℂ) • x, y⟫ = ⟪x, y⟫ * t := by
  sorry
  -- rw [inner_smul_left, conj_ofReal, mul_comm]

theorem inner_smul_ofReal_right (x y : F) {t : ℝ} : ⟪x, (t : ℂ) • y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_right, mul_comm]

theorem re_inner_smul_ofReal_smul_self (x : F) {t : ℝ} :
    re ⟪(t : ℂ) • x, (t : ℂ) • x⟫ = normSqF x * t * t := by
  sorry
  -- apply ofReal_injective (K := ℂ)
  -- simp [inner_self_ofReal_re, inner_smul_ofReal_left, inner_smul_ofReal_right, normSq]

/-- An auxiliary equality useful to prove the **Cauchy–Schwarz inequality**. Here we use the
standard argument involving the discriminant of quadratic form. -/
lemma cauchy_schwarz_aux' (x y : F) (t : ℝ) : 0 ≤ normSqF x * t * t + 2 * re ⟪x, y⟫ * t
    + normSqF y := by
  sorry
  -- calc 0 ≤ re ⟪(ofReal t : ℂ) • x + y, (ofReal t : ℂ) • x + y⟫ := inner_self_nonneg
  -- _ = re (⟪(ofReal t : ℂ) • x, (ofReal t : ℂ) • x⟫ + ⟪(ofReal t : ℂ) • x, y⟫
  --     + ⟪y, (ofReal t : ℂ) • x⟫ + ⟪y, y⟫) := by rw [inner_add_add_self ((ofReal t : ℂ) • x) y]
  -- _ = re ⟪(ofReal t : ℂ) • x, (ofReal t : ℂ) • x⟫
  --     + re ⟪(ofReal t : ℂ) • x, y⟫ + re ⟪y, (ofReal t : ℂ) • x⟫ + re ⟪y, y⟫ := by
  --     simp only [map_add]
  -- _ = normSq x * t * t + re (⟪x, y⟫ * t) + re (⟪y, x⟫ * t) + re ⟪y, y⟫ := by rw
  --   [re_inner_smul_ofReal_smul_self, inner_smul_ofReal_left, inner_smul_ofReal_right]
  -- _ = normSq x * t * t + re ⟪x, y⟫ * t + re ⟪y, x⟫ * t + re ⟪y, y⟫ := by rw [mul_comm ⟪x,y⟫ _,
  --   RCLike.re_ofReal_mul, mul_comm t _, mul_comm ⟪y,x⟫ _, RCLike.re_ofReal_mul, mul_comm t _]
  -- _ = normSq x * t * t + re ⟪x, y⟫ * t + re ⟪y, x⟫ * t + normSq y := by rw [← normSq]
  -- _ = normSq x * t * t + re ⟪x, y⟫ * t + re ⟪x, y⟫ * t + normSq y := by rw [inner_re_symm]
  -- _ = normSq x * t * t + 2 * re ⟪x, y⟫ * t + normSq y := by ring

/-- Another auxiliary equality related with the **Cauchy–Schwarz inequality**: the square of the
seminorm of `⟪x, y⟫ • x - ⟪x, x⟫ • y` is equal to `‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫‖ ^ 2)`.
We use `InnerProductSpace.ofCore.normSq x` etc (defeq to `is_R_or_C.re ⟪x, x⟫`) instead of `‖x‖ ^ 2`
etc to avoid extra rewrites when applying it to an `InnerProductSpace`. -/
theorem cauchy_schwarz_aux (x y : F) : normSqF (⟪x, y⟫ • x - ⟪x, x⟫ • y)
    = normSqF x * (normSqF x * normSqF y - ‖⟪x, y⟫‖ ^ 2) := by
  sorry
  -- rw [← @ofReal_inj ℂ, ofReal_normSq_eq_inner_self]
  -- simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, conj_ofReal, mul_sub, ←
  --   ofReal_normSq_eq_inner_self x, ← ofReal_normSq_eq_inner_self y]
  -- rw [← mul_assoc, mul_conj, RCLike.conj_mul, mul_left_comm, ← inner_conj_symm y, mul_conj]
  -- push_cast
  -- ring

/-- **Cauchy–Schwarz inequality**.
We need this for the `PreInnerProductSpace.Core` structure to prove the triangle inequality below
when showing the core is a normed group and to take the quotient.
-/
theorem inner_mul_inner_self_le (x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := by
  suffices discrim (normSqF x) (2 * ‖⟪x, y⟫‖) (normSqF y) ≤ 0 by
    rw [norm_inner_symm y x]
    rw [discrim, normSq, normSq, sq] at this
    linarith
  refine discrim_le_zero fun t ↦ ?_
  by_cases hzero : ⟪x, y⟫ = 0
  · simp only [mul_assoc, ← sq, hzero, norm_zero, mul_zero, zero_mul, add_zero, ge_iff_le]
    obtain ⟨hx, hy⟩ : (0 ≤ normSqF x ∧ 0 ≤ normSqF y) := ⟨inner_self_nonneg, inner_self_nonneg⟩
    positivity
  · have hzero' : ‖⟪x, y⟫‖ ≠ 0 := norm_ne_zero_iff.2 hzero
    convert cauchy_schwarz_aux' (⟪x, y⟫ • x) y (t / ‖⟪x, y⟫‖) using 3
    · field_simp
      rw [← sq, normSq, normSq, inner_smul_right, inner_smul_left, ← mul_assoc _ _ ⟪x, x⟫,
        mul_conj]
      nth_rw 2 [sq]
      sorry
      -- rw [← ofReal_mul, re_ofReal_mul]
      -- ring
    · field_simp
      sorry
      -- rw [inner_smul_left, mul_comm _ ⟪x, y⟫, mul_conj, ← ofReal_pow, ofReal_re]
      -- ring

/-- (Semi)norm constructed from an `PreInnerProductSpace.Core` structure, defined to be the square
root of the scalar product. -/
def toNorm : Norm F where norm x := √(re ⟪x, x⟫)

attribute [local instance] toNorm

theorem norm_eq_sqrt_inner (x : F) : ‖x‖ = √(re ⟪x, x⟫) := rfl

theorem inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [norm_eq_sqrt_inner, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫), sqrt_mul_self inner_self_nonneg]

theorem sqrt_normSq_eq_norm (x : F) : √(normSqF x) = ‖x‖ := rfl

/-- Cauchy–Schwarz inequality with norm -/
theorem norm_inner_le_norm (x y : F) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ :=
  nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) <|
    calc
      ‖⟪x, y⟫‖ * ‖⟪x, y⟫‖ = ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ := by rw [norm_inner_symm]
      _ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := inner_mul_inner_self_le x y
      _ = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) := by simp only [inner_self_eq_norm_mul_norm]; ring

/-- Seminormed group structure constructed from an `PreInnerProductSpace.Core` structure -/
def toSeminormedAddCommGroup : SeminormedAddCommGroup F :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this }

attribute [local instance] toSeminormedAddCommGroup

/-- Normed space (which is actually a seminorm) structure constructed from an
`PreInnerProductSpace.Core` structure -/
def toSeminormedSpace : NormedSpace ℂ F where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    sorry
    -- rw [RCLike.conj_mul, ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← ofReal_normSq_eq_inner_self,
    --   ofReal_re]
    -- · simp [sqrt_normSq_eq_norm, RCLike.sqrt_normSq_eq_norm]
    -- · positivity

end PreInnerProductSpace.Core

section InnerProductSpace.Core

variable [AddCommGroup F] [Module ℂ F] [cd : InnerProductSpace.Core F]

local notation "⟪" x ", " y "⟫" => @Inner F _ x y

local notation "normSqK" => @RCLike.normSq ℂ _

local notation "reK" => @RCLike.re ℂ _

local notation "ext_iff" => @RCLike.ext_iff ℂ _

local postfix:90 "†" => starRingEnd _

/-- Inner product defined by the `InnerProductSpace.Core` structure. We can't reuse
`InnerProductSpace.Core.toInner` because it takes `InnerProductSpace.Core` as an explicit
argument. -/
def toInner' : Inner F :=
  cd.toInner

attribute [local instance] toInner'

local notation "normSqF" => @normSq F _ _ _

theorem inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  ⟨cd.definite _, inner_self_of_eq_zero⟩

theorem normSq_eq_zero {x : F} : normSqF x = 0 ↔ x = 0 :=
  Iff.trans
    (by simp only [normSq, ext_iff, map_zero, inner_self_im, eq_self_iff_true, and_true])
    (@inner_self_eq_zero _ _ _ _ x)

theorem inner_self_ne_zero {x : F} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

attribute [local instance] toNorm

/-- Normed group structure constructed from an `InnerProductSpace.Core` structure -/
def toNormedAddCommGroup : NormedAddCommGroup F :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => √(re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y => by
        have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) := by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
      eq_zero_of_map_eq_zero' := fun x hx =>
        normSq_eq_zero.1 <| (sqrt_eq_zero inner_self_nonneg).1 hx }

attribute [local instance] toNormedAddCommGroup

/-- Normed space structure constructed from an `InnerProductSpace.Core` structure -/
def toNormedSpace : NormedSpace ℂ F where
  norm_smul_le r x := by
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    sorry
    -- rw [RCLike.conj_mul, ← ofReal_pow, re_ofReal_mul, sqrt_mul, ← ofReal_normSq_eq_inner_self,
    --   ofReal_re]
    -- · simp [sqrt_normSq_eq_norm, RCLike.sqrt_normSq_eq_norm]
    -- · positivity

end InnerProductSpace.Core

end InnerProductSpace.Core

section

attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup

/-- Given an `InnerProductSpace.Core` structure on a space, one can use it to turn
the space into an inner product space. The `NormedAddCommGroup` structure is expected
to already be defined with `InnerProductSpace.ofCore.toNormedAddCommGroup`. -/
def InnerProductSpace.ofCore [AddCommGroup F] [Module ℂ F] (cd : InnerProductSpace.Core F) :
    InnerProductSpace F :=
  letI : NormedSpace ℂ F := @InnerProductSpace.Core.toNormedSpace F _ _ cd
  { cd with
    norm_sq_eq_inner := fun x => by
      sorry }
      -- have h₁ : ‖x‖ ^ 2 = √(re (cd.inner x x)) ^ 2 := rfl
      -- have h₂ : 0 ≤ re (cd.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      -- simp [h₁, sq_sqrt, h₂] }

end

/-! ### Properties of inner product spaces -/

section BasicProperties_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace E]

local notation "⟪" x ", " y "⟫" => @Inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_inner)

@[simp]
theorem inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  InnerProductSpace.conj_symm _ _

theorem inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 := by
  rw [← inner_conj_symm]
  exact star_eq_zero

@[simp]
theorem inner_self_im (x : E) : im ⟪x, x⟫ = 0 := by rw [← @ofReal_inj ℂ, im_eq_conj_sub]; simp

theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  InnerProductSpace.add_left _ _ _

theorem inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add]
  simp only [inner_conj_symm]

theorem inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

theorem inner_im_symm (x y : E) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

theorem inner_smul_left (x y : E) (r : ℂ) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  InnerProductSpace.smul_left _ _ _

theorem inner_smul_real_left (x y : E) (r : ℝ) : ⟪(r : ℂ) • x, y⟫ = r • ⟪x, y⟫ := by
  sorry
  -- rw [inner_smul_left, conj_ofReal, Algebra.smul_def]

theorem inner_smul_right (x y : E) (r : ℂ) : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left, RingHom.map_mul, conj_conj, inner_conj_symm]

theorem inner_smul_real_right (x y : E) (r : ℝ) : ⟪x, (r : ℂ) • y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_right, Algebra.smul_def]
  sorry

/-- The inner product as a sesquilinear form.

Note that in the case `ℂ = ℝ` this is a bilinear form. -/
@[simps!]
def sesqFormOfInner : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd _) (fun x y => ⟪y, x⟫)
    (fun _x _y _z => inner_add_right _ _ _) (fun _r _x _y => inner_smul_right _ _ _)
    (fun _x _y _z => inner_add_left _ _ _) fun _r _x _y => inner_smul_left _ _ _

/-- An inner product with a sum on the left. -/
theorem sum_inner {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪∑ i ∈ s, f i, x⟫ = ∑ i ∈ s, ⟪f i, x⟫ :=
  map_sum (sesqFormOfInner (E := E) x) _ _

/-- An inner product with a sum on the right. -/
theorem inner_sum {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫ :=
  map_sum (LinearMap.flip sesqFormOfInner x) _ _

/-- An inner product with a sum on the left, `Finsupp` version. -/
protected theorem Finsupp.sum_inner {ι : Type*} (l : ι →₀ ℂ) (v : ι → E) (x : E) :
    ⟪l.sum fun (i : ι) (a : ℂ) => a • v i, x⟫ = l.sum fun (i : ι) (a : ℂ) => conj a • ⟪v i, x⟫ := by
  convert sum_inner l.support (fun a => l a • v a) x
  simp only [inner_smul_left, Finsupp.sum, smul_eq_mul]

/-- An inner product with a sum on the right, `Finsupp` version. -/
protected theorem Finsupp.inner_sum {ι : Type*} (l : ι →₀ ℂ) (v : ι → E) (x : E) :
    ⟪x, l.sum fun (i : ι) (a : ℂ) => a • v i⟫ = l.sum fun (i : ι) (a : ℂ) => a • ⟪x, v i⟫ := by
  convert inner_sum l.support (fun a => l a • v a) x
  simp only [inner_smul_right, Finsupp.sum, smul_eq_mul]

protected theorem DFinsupp.sum_inner {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪l.sum f, x⟫ = l.sum fun i a => ⟪f i a, x⟫ := by
  simp (config := { contextual := true }) only [DFinsupp.sum, sum_inner, smul_eq_mul]

protected theorem DFinsupp.inner_sum {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪x, l.sum f⟫ = l.sum fun i a => ⟪x, f i a⟫ := by
  simp (config := { contextual := true }) only [DFinsupp.sum, inner_sum, smul_eq_mul]

@[simp]
theorem inner_zero_left (x : E) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul ℂ (0 : E), inner_smul_left, RingHom.map_zero, zero_mul]

theorem inner_re_zero_left (x : E) : re ⟪0, x⟫ = 0 := by
  simp only [inner_zero_left, AddMonoidHom.map_zero]

@[simp]
theorem inner_zero_right (x : E) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left, RingHom.map_zero]

theorem inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0 := by
  simp only [inner_zero_right, AddMonoidHom.map_zero]

theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ :=
  PreInnerProductSpace.toCore.nonneg_re x

@[simp]
theorem inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : ℂ) = ⟪x, x⟫ :=
  ((RCLike.is_real_TFAE (⟪x, x⟫ : ℂ)).out 2 3).2 (inner_self_im x)

theorem inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (‖x‖ : ℂ) ^ 2 := by
  sorry
  -- rw [← inner_self_ofReal_re, ← norm_sq_eq_inner, ofReal_pow]

theorem inner_self_re_eq_norm (x : E) : re ⟪x, x⟫ = ‖⟪x, x⟫‖ := by
  conv_rhs => rw [← inner_self_ofReal_re]
  symm
  exact norm_of_nonneg inner_self_nonneg

theorem inner_self_ofReal_norm (x : E) : (‖⟪x, x⟫‖ : ℂ) = ⟪x, x⟫ := by
  rw [← inner_self_re_eq_norm]
  exact inner_self_ofReal_re _

theorem norm_inner_symm (x y : E) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]

@[simp]
theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul ℂ x, inner_smul_left]
  simp

@[simp]
theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left]; simp only [RingHom.map_neg, inner_conj_symm]

theorem inner_neg_neg (x y : E) : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

-- Porting note: removed `simp` because it can prove it using `inner_conj_symm`
theorem inner_self_conj (x : E) : ⟪x, x⟫† = ⟪x, x⟫ := inner_conj_symm _ _

theorem inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]

theorem inner_mul_symm_re_eq_norm (x y : E) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]
  exact re_eq_norm_of_mul_conj (inner y x)

/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

-- Expand `⟪x - y, x - y⟫`
theorem inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring

/-- Parallelogram law -/
theorem parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) := by
  simp only [inner_add_add_self, inner_sub_sub_self]
  ring

/-- **Cauchy–Schwarz inequality**. -/
theorem inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
  letI cd : PreInnerProductSpace.Core E := PreInnerProductSpace.toCore
  InnerProductSpace.Core.inner_mul_inner_self_le x y

end BasicProperties_Seminormed

section BasicProperties

variable [NormedAddCommGroup E] [InnerProductSpace E]

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_inner)

@[simp]
theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  sorry
  -- rw [inner_self_eq_norm_sq_to_K, sq_eq_zero_iff, ofReal_eq_zero, norm_eq_zero]

theorem inner_self_ne_zero {x : E} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

theorem ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero, inner_sub_right, sub_eq_zero, h (x - y)]

theorem ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero, inner_sub_left, sub_eq_zero, h (x - y)]

@[simp]
theorem inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 := by
  rw [← norm_sq_eq_inner, (sq_nonneg _).le_iff_eq, sq_eq_zero_iff, norm_eq_zero]

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
theorem linearIndependent_of_ne_zero_of_inner_eq_zero {ι : Type*} {v : ι → E} (hz : ∀ i, v i ≠ 0)
    (ho : Pairwise fun i j => ⟪v i, v j⟫ = 0) : LinearIndependent ℂ v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h' : g i * inner (v i) (v i) = inner (v i) (∑ j ∈ s, g j • v j) := by
    rw [inner_sum]
    symm
    convert Finset.sum_eq_single (β := ℂ) i ?_ ?_
    · rw [inner_smul_right]
    · intro j _hj hji
      rw [inner_smul_right, ho hji.symm, mul_zero]
    · exact fun h => False.elim (h hi)
  simpa [hg, hz] using h'

end BasicProperties

section OrthonormalSets_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace E]
-- variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

variable {ι : Type*}

/-- An orthonormal set of vectors in an `InnerProductSpace` -/
def Orthonormal (v : ι → E) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ Pairwise fun i j => ⟪v i, v j⟫ = 0

/-- `if ... then ... else` characterization of an indexed set of vectors being orthonormal.  (Inner
product equals Kronecker delta.) -/
theorem orthonormal_iff_ite [DecidableEq ι] {v : ι → E} :
    Orthonormal v ↔ ∀ i j, ⟪v i, v j⟫ = if i = j then (1 : ℂ) else (0 : ℂ) := by
  constructor
  · intro hv i j
    split_ifs with h
    · simp [h, inner_self_eq_norm_sq_to_K, hv.1]
    · exact hv.2 h
  · intro h
    constructor
    · intro i
      have h' : ‖v i‖ ^ 2 = 1 ^ 2 := by simp [@norm_sq_eq_inner, h i i]
      have h₁ : 0 ≤ ‖v i‖ := norm_nonneg _
      have h₂ : (0 : ℝ) ≤ 1 := zero_le_one
      rwa [sq_eq_sq h₁ h₂] at h'
    · intro i j hij
      simpa [hij] using h i j

/-- `if ... then ... else` characterization of a set of vectors being orthonormal.  (Inner product
equals Kronecker delta.) -/
theorem orthonormal_subtype_iff_ite [DecidableEq E] {s : Set E} :
    Orthonormal (Subtype.val : s → E) ↔ ∀ v ∈ s, ∀ w ∈ s, ⟪v, w⟫ = if v = w then 1 else 0 := by
  rw [orthonormal_iff_ite]
  constructor
  · intro h v hv w hw
    convert h ⟨v, hv⟩ ⟨w, hw⟩ using 1
    simp
  · rintro h ⟨v, hv⟩ ⟨w, hw⟩
    convert h v hv w hw using 1
    simp

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_finsupp {v : ι → E} (hv : Orthonormal v) (l : ι →₀ ℂ) (i : ι) :
    ⟪v i, linearCombination ℂ v l⟫ = l i := by
  classical
  simpa [linearCombination_apply, Finsupp.inner_sum, orthonormal_iff_ite.mp hv] using Eq.symm

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_sum {v : ι → E} (hv : Orthonormal v) (l : ι → ℂ) {s : Finset ι}
    {i : ι} (hi : i ∈ s) : ⟪v i, ∑ i ∈ s, l i • v i⟫ = l i := by
  classical
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv, hi]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal v) (l : ι → ℂ)
    (i : ι) : ⟪v i, ∑ i : ι, l i • v i⟫ = l i :=
  hv.inner_right_sum l (Finset.mem_univ _)

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_finsupp {v : ι → E} (hv : Orthonormal v) (l : ι →₀ ℂ) (i : ι) :
    ⟪linearCombination ℂ v l, v i⟫ = conj (l i) := by rw [← inner_conj_symm, hv.inner_right_finsupp]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_sum {v : ι → E} (hv : Orthonormal v) (l : ι → ℂ) {s : Finset ι}
    {i : ι} (hi : i ∈ s) : ⟪∑ i ∈ s, l i • v i, v i⟫ = conj (l i) := by
  classical
  simp only [sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv, hi, mul_boole,
    Finset.sum_ite_eq', if_true]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal v) (l : ι → ℂ)
    (i : ι) : ⟪∑ i : ι, l i • v i, v i⟫ = conj (l i) :=
  hv.inner_left_sum l (Finset.mem_univ _)

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the first `Finsupp`. -/
theorem Orthonormal.inner_finsupp_eq_sum_left {v : ι → E} (hv : Orthonormal v) (l₁ l₂ : ι →₀ ℂ) :
    ⟪linearCombination ℂ v l₁, linearCombination ℂ v l₂⟫ = l₁.sum fun i y => conj y * l₂ i := by
  simp only [l₁.linearCombination_apply _, Finsupp.sum_inner, hv.inner_right_finsupp, smul_eq_mul]

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the second `Finsupp`. -/
theorem Orthonormal.inner_finsupp_eq_sum_right {v : ι → E} (hv : Orthonormal v) (l₁ l₂ : ι →₀ ℂ) :
    ⟪linearCombination ℂ v l₁, linearCombination ℂ v l₂⟫ = l₂.sum fun i y => conj (l₁ i) * y := by
  simp only [l₂.linearCombination_apply _, Finsupp.inner_sum, hv.inner_left_finsupp, mul_comm,
             smul_eq_mul]

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum. -/
protected theorem Orthonormal.inner_sum {v : ι → E} (hv : Orthonormal v) (l₁ l₂ : ι → ℂ)
    (s : Finset ι) : ⟪∑ i ∈ s, l₁ i • v i, ∑ i ∈ s, l₂ i • v i⟫ = ∑ i ∈ s, conj (l₁ i) * l₂ i := by
  simp_rw [sum_inner, inner_smul_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hv.inner_right_sum l₂ hi]

/--
The double sum of weighted inner products of pairs of vectors from an orthonormal sequence is the
sum of the weights.
-/
theorem Orthonormal.inner_left_right_finset {s : Finset ι} {v : ι → E} (hv : Orthonormal v)
    {a : ι → ι → ℂ} : (∑ i ∈ s, ∑ j ∈ s, a i j • ⟪v j, v i⟫) = ∑ k ∈ s, a k k := by
  classical
  simp [orthonormal_iff_ite.mp hv, Finset.sum_ite_of_true]

/-- An orthonormal set is linearly independent. -/
theorem Orthonormal.linearIndependent {v : ι → E} (hv : Orthonormal v) :
    LinearIndependent ℂ v := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have key : ⟪v i, Finsupp.linearCombination ℂ v l⟫ = ⟪v i, 0⟫ := by rw [hl]
  simpa only [hv.inner_right_finsupp, inner_zero_right] using key

/-- A subfamily of an orthonormal family (i.e., a composition with an injective map) is an
orthonormal family. -/
theorem Orthonormal.comp {ι' : Type*} {v : ι → E} (hv : Orthonormal v) (f : ι' → ι)
    (hf : Function.Injective f) : Orthonormal (v ∘ f) := by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  convert hv (f i) (f j) using 1
  simp [hf.eq_iff]

/-- An injective family `v : ι → E` is orthonormal if and only if `Subtype.val : (range v) → E` is
orthonormal. -/
theorem orthonormal_subtype_range {v : ι → E} (hv : Function.Injective v) :
    Orthonormal (Subtype.val : Set.range v → E) ↔ Orthonormal v := by
  let f : ι ≃ Set.range v := Equiv.ofInjective v hv
  refine ⟨fun h => h.comp f f.injective, fun h => ?_⟩
  rw [← Equiv.self_comp_ofInjective_symm hv]
  exact h.comp f.symm f.symm.injective

/-- If `v : ι → E` is an orthonormal family, then `Subtype.val : (range v) → E` is an orthonormal
family. -/
theorem Orthonormal.toSubtypeRange {v : ι → E} (hv : Orthonormal v) :
    Orthonormal (Subtype.val : Set.range v → E) :=
  (orthonormal_subtype_range hv.linearIndependent.injective).2 hv

/-- A linear combination of some subset of an orthonormal set is orthogonal to other members of the
set. -/
theorem Orthonormal.inner_finsupp_eq_zero {v : ι → E} (hv : Orthonormal v) {s : Set ι} {i : ι}
    (hi : i ∉ s) {l : ι →₀ ℂ} (hl : l ∈ Finsupp.supported ℂ ℂ s) :
    ⟪Finsupp.linearCombination ℂ v l, v i⟫ = 0 := by
  rw [Finsupp.mem_supported'] at hl
  simp only [hv.inner_left_finsupp, hl i hi, map_zero]

/-- Given an orthonormal family, a second family of vectors is orthonormal if every vector equals
the corresponding vector in the original family or its negation. -/
theorem Orthonormal.orthonormal_of_forall_eq_or_eq_neg {v w : ι → E} (hv : Orthonormal v)
    (hw : ∀ i, w i = v i ∨ w i = -v i) : Orthonormal w := by
  classical
  rw [orthonormal_iff_ite] at *
  intro i j
  cases' hw i with hi hi <;> cases' hw j with hj hj <;>
    replace hv := hv i j <;> split_ifs at hv ⊢ with h <;>
    simpa only [hi, hj, h, inner_neg_right, inner_neg_left, neg_neg, eq_self_iff_true,
      neg_eq_zero] using hv

/- The material that follows, culminating in the existence of a maximal orthonormal subset, is
adapted from the corresponding development of the theory of linearly independents sets.  See
`exists_linearIndependent` in particular. -/
variable (E)

theorem orthonormal_empty : Orthonormal (fun x => x : (∅ : Set E) → E) := by
  classical
  simp [orthonormal_subtype_iff_ite]

variable {E}

theorem orthonormal_iUnion_of_directed {η : Type*} {s : η → Set E} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, Orthonormal (fun x => x : s i → E)) :
    Orthonormal (fun x => x : (⋃ i, s i) → E) := by
  classical
  rw [orthonormal_subtype_iff_ite]
  rintro x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩
  obtain ⟨k, hik, hjk⟩ := hs i j
  have h_orth : Orthonormal (fun x => x : s k → E) := h k
  rw [orthonormal_subtype_iff_ite] at h_orth
  exact h_orth x (hik hxi) y (hjk hyj)

theorem orthonormal_sUnion_of_directed {s : Set (Set E)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, Orthonormal (fun x => ((x : a) : E))) :
    Orthonormal (fun x => x : ⋃₀ s → E) := by
  rw [Set.sUnion_eq_iUnion]; exact orthonormal_iUnion_of_directed hs.directed_val (by simpa using h)

/-- Given an orthonormal set `v` of vectors in `E`, there exists a maximal orthonormal set
containing it. -/
theorem exists_maximal_orthonormal {s : Set E} (hs : Orthonormal (Subtype.val : s → E)) :
    ∃ w ⊇ s, Orthonormal (Subtype.val : w → E) ∧
      ∀ u ⊇ w, Orthonormal (Subtype.val : u → E) → u = w := by
  have := zorn_subset_nonempty { b | Orthonormal (Subtype.val : b → E) } ?_ _ hs
  · obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.1, hb.2.1, fun u hus hu => hb.2.eq_of_ge hu hus ⟩
  · refine fun c hc cc _c0 => ⟨⋃₀ c, ?_, ?_⟩
    · exact orthonormal_sUnion_of_directed cc.directedOn fun x xc => hc xc
    · exact fun _ => Set.subset_sUnion_of_mem

open FiniteDimensional

/-- A family of orthonormal vectors with the correct cardinality forms a basis. -/
def basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E} (hv : Orthonormal v)
    (card_eq : Fintype.card ι = finrank ℂ E) : Basis ι ℂ E :=
  basisOfLinearIndependentOfCardEqFinrank hv.linearIndependent card_eq

@[simp]
theorem coe_basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E}
    (hv : Orthonormal v) (card_eq : Fintype.card ι = finrank ℂ E) :
    (basisOfOrthonormalOfCardEqFinrank hv card_eq : ι → E) = v :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem Orthonormal.ne_zero {v : ι → E} (hv : Orthonormal v) (i : ι) : v i ≠ 0 := by
  refine ne_of_apply_ne norm ?_
  rw [hv.1 i, norm_zero]
  norm_num

end OrthonormalSets_Seminormed

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace E]

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

theorem norm_eq_sqrt_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫) :=
  calc
    ‖x‖ = √(‖x‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ = √(re ⟪x, x⟫) := congr_arg _ (norm_sq_eq_inner _)

theorem inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [@norm_eq_sqrt_inner, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
    sqrt_mul_self inner_self_nonneg]

theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^ 2 := by
  rw [pow_two, inner_self_eq_norm_mul_norm]

-- Porting note: this was present in mathlib3 but seemingly didn't do anything.
-- variable (ℂ)

/-- Expand the square -/
theorem norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  repeat' rw [sq (M := ℝ), ← @inner_self_eq_norm_mul_norm]
  rw [inner_add_add_self, two_mul]
  simp only [add_assoc, add_left_inj, add_right_inj, AddMonoidHom.map_add]
  rw [← inner_conj_symm, conj_re]

alias norm_add_pow_two := norm_add_sq

/-- Expand the square -/
theorem norm_add_mul_self (x y : E) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by
  repeat' rw [← sq (M := ℝ)]
  exact norm_add_sq _ _

/-- Expand the square -/
theorem norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  rw [sub_eq_add_neg, @norm_add_sq _ _ _ x (-y), norm_neg, inner_neg_right, map_neg, mul_neg,
    sub_eq_add_neg]

alias norm_sub_pow_two := norm_sub_sq

/-- Expand the square -/
theorem norm_sub_mul_self (x y : E) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by
  repeat' rw [← sq (M := ℝ)]
  exact norm_sub_sq _ _

/-- Cauchy–Schwarz inequality with norm -/
theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_eq_sqrt_inner x, norm_eq_sqrt_inner y]
  letI : PreInnerProductSpace.Core E := PreInnerProductSpace.toCore
  exact InnerProductSpace.Core.norm_inner_le_norm x y

theorem nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ ≤ ‖x‖₊ * ‖y‖₊ :=
  norm_inner_le_norm x y

theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
  le_trans (re_le_norm (inner x y)) (norm_inner_le_norm x y)

theorem parallelogram_law_with_norm (x y : E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  simp only [← @inner_self_eq_norm_mul_norm]
  rw [← re.map_add, parallelogram_law, two_mul, two_mul]
  simp only [re.map_add]

theorem parallelogram_law_with_nnnorm (x y : E) :
    ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊) :=
  Subtype.ext <| parallelogram_law_with_norm x y

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 := by
  rw [@norm_add_mul_self]
  ring

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 := by
  rw [@norm_sub_mul_self]
  ring

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4 := by
  rw [@norm_add_mul_self, @norm_sub_mul_self]
  ring

/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
theorem im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (x y : E) :
    im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • y‖ * ‖x + IK • y‖) / 4 := by
  simp only [@norm_add_mul_self, @norm_sub_mul_self, inner_smul_right, I_mul_re]
  ring

/-- Polarization identity: The inner product, in terms of the norm. -/
theorem inner_eq_sum_norm_sq_div_four (x y : E) :
    ⟪x, y⟫ = ((‖x + y‖ : ℂ) ^ 2 - (‖x - y‖ : ℂ) ^ 2 +
              ((‖x - IK • y‖ : ℂ) ^ 2 - (‖x + IK • y‖ : ℂ) ^ 2) * IK) / 4 := by
  rw [← re_add_im ⟪x, y⟫, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
  push_cast
  simp only [sq, ← mul_div_right_comm, ← add_div]
  sorry

section Complex_Seminormed

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace V]

/-- A complex polarization identity, with a linear map
-/
theorem inner_map_polarization (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T y, x⟫ =
      (⟪T (x + y), x + y⟫ - ⟪T (x - y), x - y⟫ +
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫ -
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, LinearMap.map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, sub_neg_eq_add, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

theorem inner_map_polarization' (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T x, y⟫ =
      (⟪T (x + y), x + y⟫ - ⟪T (x - y), x - y⟫ -
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫ +
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, LinearMap.map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, sub_neg_eq_add, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

end Complex_Seminormed

section Complex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace V]

/-- A linear map `T` is zero, if and only if the identity `⟪T x, x⟫ = 0` holds for all `x`.
-/
theorem inner_map_self_eq_zero (T : V →ₗ[ℂ] V) : (∀ x : V, ⟪T x, x⟫ = 0) ↔ T = 0 := by
  constructor
  · intro hT
    ext x
    rw [LinearMap.zero_apply, ← @inner_self_eq_zero V, inner_map_polarization]
    simp only [hT]
    norm_num
  · rintro rfl x
    simp only [LinearMap.zero_apply, inner_zero_left]

/--
Two linear maps `S` and `T` are equal, if and only if the identity `⟪S x, x⟫ = ⟪T x, x⟫` holds
for all `x`.
-/
theorem ext_inner_map (S T : V →ₗ[ℂ] V) : (∀ x : V, ⟪S x, x⟫ = ⟪T x, x⟫) ↔ S = T := by
  rw [← sub_eq_zero, ← inner_map_self_eq_zero]
  refine forall_congr' fun x => ?_
  rw [LinearMap.sub_apply, inner_sub_left, sub_eq_zero]

end Complex

section

variable {ι : Type*} {ι' : Type*} {ι'' : Type*}
variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace E']
variable {E'' : Type*} [SeminormedAddCommGroup E''] [InnerProductSpace E'']

/-- A linear isometry preserves the inner product. -/
@[simp]
theorem LinearIsometry.inner_map_map (f : E →ₗᵢ[ℂ] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ := by
  simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]

/-- A linear isometric equivalence preserves the inner product. -/
@[simp]
theorem LinearIsometryEquiv.inner_map_map (f : E ≃ₗᵢ[ℂ] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
  f.toLinearIsometry.inner_map_map x y

/-- The adjoint of a linear isometric equivalence is its inverse. -/
theorem LinearIsometryEquiv.inner_map_eq_flip (f : E ≃ₗᵢ[ℂ] E') (x : E) (y : E') :
    ⟪f x, y⟫ = ⟪x, f.symm y⟫ := by
  conv_lhs => rw [← f.apply_symm_apply y, f.inner_map_map]

/-- A linear map that preserves the inner product is a linear isometry. -/
def LinearMap.isometryOfInner (f : E →ₗ[ℂ] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[ℂ] E' :=
  ⟨f, fun x => by simp only [@norm_eq_sqrt_inner, h]⟩

@[simp]
theorem LinearMap.coe_isometryOfInner (f : E →ₗ[ℂ] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
theorem LinearMap.isometryOfInner_toLinearMap (f : E →ₗ[ℂ] E') (h) :
    (f.isometryOfInner h).toLinearMap = f :=
  rfl

/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
def LinearEquiv.isometryOfInner (f : E ≃ₗ[ℂ] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[ℂ] E' :=
  ⟨f, ((f : E →ₗ[ℂ] E').isometryOfInner h).norm_map⟩

@[simp]
theorem LinearEquiv.coe_isometryOfInner (f : E ≃ₗ[ℂ] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
theorem LinearEquiv.isometryOfInner_toLinearEquiv (f : E ≃ₗ[ℂ] E') (h) :
    (f.isometryOfInner h).toLinearEquiv = f :=
  rfl

/-- A linear map is an isometry if and it preserves the inner product. -/
theorem LinearMap.norm_map_iff_inner_map_map {F : Type*} [FunLike F E E'] [LinearMapClass F ℂ E E']
    (f : F) : (∀ x, ‖f x‖ = ‖x‖) ↔ (∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) :=
  ⟨({ toLinearMap := LinearMapClass.linearMap f, norm_map' := · : E →ₗᵢ[ℂ] E' }.inner_map_map),
    (LinearMapClass.linearMap f |>.isometryOfInner · |>.norm_map)⟩

/-- A linear isometry preserves the property of being orthonormal. -/
theorem LinearIsometry.orthonormal_comp_iff {v : ι → E} (f : E →ₗᵢ[ℂ] E') :
    Orthonormal (f ∘ v) ↔ Orthonormal v := by
  classical simp_rw [orthonormal_iff_ite, Function.comp_apply, LinearIsometry.inner_map_map]

/-- A linear isometry preserves the property of being orthonormal. -/
theorem Orthonormal.comp_linearIsometry {v : ι → E} (hv : Orthonormal v) (f : E →ₗᵢ[ℂ] E') :
    Orthonormal (f ∘ v) := by rwa [f.orthonormal_comp_iff]

/-- A linear isometric equivalence preserves the property of being orthonormal. -/
theorem Orthonormal.comp_linearIsometryEquiv {v : ι → E} (hv : Orthonormal v) (f : E ≃ₗᵢ[ℂ] E') :
    Orthonormal (f ∘ v) :=
  hv.comp_linearIsometry f.toLinearIsometry

/-- A linear isometric equivalence, applied with `Basis.map`, preserves the property of being
orthonormal. -/
theorem Orthonormal.mapLinearIsometryEquiv {v : Basis ι ℂ E} (hv : Orthonormal v)
    (f : E ≃ₗᵢ[ℂ] E') : Orthonormal (v.map f.toLinearEquiv) :=
  hv.comp_linearIsometryEquiv f

/-- A linear map that sends an orthonormal basis to orthonormal vectors is a linear isometry. -/
def LinearMap.isometryOfOrthonormal (f : E →ₗ[ℂ] E') {v : Basis ι ℂ E} (hv : Orthonormal v)
    (hf : Orthonormal (f ∘ v)) : E →ₗᵢ[ℂ] E' :=
  f.isometryOfInner fun x y => by
    classical rw [← v.linearCombination_repr x, ← v.linearCombination_repr y,
      Finsupp.apply_linearCombination, Finsupp.apply_linearCombination,
      hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]

@[simp]
theorem LinearMap.coe_isometryOfOrthonormal (f : E →ₗ[ℂ] E') {v : Basis ι ℂ E}
    (hv : Orthonormal v) (hf : Orthonormal (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl

@[simp]
theorem LinearMap.isometryOfOrthonormal_toLinearMap (f : E →ₗ[ℂ] E') {v : Basis ι ℂ E}
    (hv : Orthonormal v) (hf : Orthonormal (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearMap = f :=
  rfl

/-- A linear equivalence that sends an orthonormal basis to orthonormal vectors is a linear
isometric equivalence. -/
def LinearEquiv.isometryOfOrthonormal (f : E ≃ₗ[ℂ] E') {v : Basis ι ℂ E} (hv : Orthonormal v)
    (hf : Orthonormal (f ∘ v)) : E ≃ₗᵢ[ℂ] E' :=
  f.isometryOfInner fun x y => by
    rw [← LinearEquiv.coe_coe] at hf
    classical rw [← v.linearCombination_repr x, ← v.linearCombination_repr y,
      ← LinearEquiv.coe_coe f, Finsupp.apply_linearCombination,
      Finsupp.apply_linearCombination, hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]

@[simp]
theorem LinearEquiv.coe_isometryOfOrthonormal (f : E ≃ₗ[ℂ] E') {v : Basis ι ℂ E}
    (hv : Orthonormal v) (hf : Orthonormal (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl

@[simp]
theorem LinearEquiv.isometryOfOrthonormal_toLinearEquiv (f : E ≃ₗ[ℂ] E') {v : Basis ι ℂ E}
    (hv : Orthonormal v) (hf : Orthonormal (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearEquiv = f :=
  rfl

/-- A linear isometric equivalence that sends an orthonormal basis to a given orthonormal basis. -/
def Orthonormal.equiv {v : Basis ι ℂ E} (hv : Orthonormal v) {v' : Basis ι' ℂ E'}
    (hv' : Orthonormal v') (e : ι ≃ ι') : E ≃ₗᵢ[ℂ] E' :=
  (v.equiv v' e).isometryOfOrthonormal hv
    (by
      have h : v.equiv v' e ∘ v = v' ∘ e := by
        ext i
        simp
      rw [h]
      classical exact hv'.comp _ e.injective)

@[simp]
theorem Orthonormal.equiv_toLinearEquiv {v : Basis ι ℂ E} (hv : Orthonormal v)
    {v' : Basis ι' ℂ E'} (hv' : Orthonormal v') (e : ι ≃ ι') :
    (hv.equiv hv' e).toLinearEquiv = v.equiv v' e :=
  rfl

@[simp]
theorem Orthonormal.equiv_apply {ι' : Type*} {v : Basis ι ℂ E} (hv : Orthonormal v)
    {v' : Basis ι' ℂ E'} (hv' : Orthonormal v') (e : ι ≃ ι') (i : ι) :
    hv.equiv hv' e (v i) = v' (e i) :=
  Basis.equiv_apply _ _ _ _

@[simp]
theorem Orthonormal.equiv_trans {v : Basis ι ℂ E} (hv : Orthonormal v) {v' : Basis ι' ℂ E'}
    (hv' : Orthonormal v') (e : ι ≃ ι') {v'' : Basis ι'' ℂ E''} (hv'' : Orthonormal v'')
    (e' : ι' ≃ ι'') : (hv.equiv hv' e).trans (hv'.equiv hv'' e') = hv.equiv hv'' (e.trans e') :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [LinearIsometryEquiv.trans_apply, Orthonormal.equiv_apply, e.coe_trans,
      Function.comp_apply]

theorem Orthonormal.map_equiv {v : Basis ι ℂ E} (hv : Orthonormal v) {v' : Basis ι' ℂ E'}
    (hv' : Orthonormal v') (e : ι ≃ ι') :
    v.map (hv.equiv hv' e).toLinearEquiv = v'.reindex e.symm :=
  v.map_equiv _ _

end

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ := by
  rw [@norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero]
  apply Or.inr
  simp only [h, zero_re']

/-- Given two orthogonal vectors, their sum and difference have equal norms. -/
theorem norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ‖w - v‖ = ‖w + v‖ := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [h, ← @inner_self_eq_norm_mul_norm, sub_neg_eq_add, sub_zero, map_sub, zero_re',
    zero_sub, add_zero, map_add, inner_add_right, inner_sub_left, inner_sub_right, inner_re_symm,
    zero_add]

/-- The inner product as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _

@[simp]
theorem innerₛₗ_apply_coe (v : E) : ⇑(innerₛₗ v) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem innerₛₗ_apply (v w : E) : innerₛₗ v w = ⟪v, w⟫ :=
  rfl

/-- The inner product as a continuous sesquilinear map. Note that `toDualMap` (resp. `toDual`)
in `InnerProductSpace.Dual` is a version of this given as a linear isometry (resp. linear
isometric equivalence). -/
def innerSL : E →L⋆[ℂ] E →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂ (innerₛₗ) 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply]

@[simp]
theorem innerSL_apply_coe (v : E) : ⇑(innerSL v) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem innerSL_apply (v w : E) : innerSL v w = ⟪v, w⟫ :=
  rfl

/-- The inner product as a continuous sesquilinear map, with the two arguments flipped. -/
def innerSLFlip : E →L[ℂ] E →L⋆[ℂ] ℂ :=
  @ContinuousLinearMap.flipₗᵢ' ℂ ℂ ℂ E E ℂ _ _ _ _ _ _ _ _ _ (RingHom.id ℂ) (starRingEnd ℂ) _ _
    (innerSL)

@[simp]
theorem innerSLFlip_apply (x y : E) : innerSLFlip x y = ⟪y, x⟫ :=
  rfl

namespace ContinuousLinearMap

variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace E']

-- Note: odd and expensive build behavior is explicitly turned off using `noncomputable`
/-- Given `f : E →L[ℂ] E'`, construct the continuous sesquilinear form `fun x y ↦ ⟪x, A y⟫`, given
as a continuous linear map. -/
noncomputable def toSesqForm : (E →L[ℂ] E') →L[ℂ] E' →L⋆[ℂ] E →L[ℂ] ℂ :=
  (ContinuousLinearMap.flipₗᵢ' E E' ℂ (starRingEnd ℂ) (RingHom.id ℂ)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' →L⋆[ℂ] ℂ) (RingHom.id ℂ) (RingHom.id ℂ) (innerSLFlip)

@[simp]
theorem toSesqForm_apply_coe (f : E →L[ℂ] E') (x : E') : toSesqForm f x = (innerSL x).comp f :=
  rfl

theorem toSesqForm_apply_norm_le {f : E →L[ℂ] E'} {v : E'} : ‖toSesqForm f v‖ ≤ ‖f‖ * ‖v‖ := by
  refine opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have h₁ : ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
  have h₂ := @norm_inner_le_norm E' _ _ v (f x)
  calc
    ‖⟪v, f x⟫‖ ≤ ‖v‖ * ‖f x‖ := h₂
    _ ≤ ‖v‖ * (‖f‖ * ‖x‖) := mul_le_mul_of_nonneg_left h₁ (norm_nonneg v)
    _ = ‖f‖ * ‖v‖ * ‖x‖ := by ring


end ContinuousLinearMap

section

variable {ι : Type*} {ι' : Type*} {ι'' : Type*}
variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace E']
variable {E'' : Type*} [SeminormedAddCommGroup E''] [InnerProductSpace E'']

@[simp]
theorem Orthonormal.equiv_refl {v : Basis ι ℂ E} (hv : Orthonormal v) :
    hv.equiv hv (Equiv.refl ι) = LinearIsometryEquiv.refl ℂ E :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [Orthonormal.equiv_apply, Equiv.coe_refl, id, LinearIsometryEquiv.coe_refl]

@[simp]
theorem Orthonormal.equiv_symm {v : Basis ι ℂ E} (hv : Orthonormal v) {v' : Basis ι' ℂ E'}
    (hv' : Orthonormal v') (e : ι ≃ ι') : (hv.equiv hv' e).symm = hv'.equiv hv e.symm :=
  v'.ext_linearIsometryEquiv fun i =>
    (hv.equiv hv' e).injective <| by
      simp only [LinearIsometryEquiv.apply_symm_apply, Orthonormal.equiv_apply, e.apply_symm_apply]

end

/-- `innerSL` is an isometry. Note that the associated `LinearIsometry` is defined in
`InnerProductSpace.Dual` as `toDualMap`. -/
@[simp]
theorem innerSL_apply_norm (x : E) : ‖innerSL x‖ = ‖x‖ := by
  sorry
--   refine
--     le_antisymm ((innerSL x).opNorm_le_bound (norm_nonneg _) fun y => norm_inner_le_norm _ _) ?_
--   rcases (norm_nonneg x).eq_or_gt with (h | h)
--   · simp [h]
--   · refine (mul_le_mul_right h).mp ?_
--     calc
--       ‖x‖ * ‖x‖ = ‖(⟪x, x⟫ : ℂ)‖ := by
--         rw [← sq, inner_self_eq_norm_sq_to_K, norm_pow, norm_ofReal, abs_norm]
--       _ ≤ ‖innerSL x‖ * ‖x‖ := (innerSL x).le_opNorm _

-- lemma norm_innerSL_le : ‖innerSL (E := E)‖ ≤ 1 :=
--   ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp)

-- /-- When an inner product space `E` over `ℂ` is considered as a real normed space, its inner
-- product satisfies `IsBoundedBilinearMap`.

-- In order to state these results, we need a `NormedSpace ℝ E` instance. We will later establish
-- such an instance by restriction-of-scalars, `InnerProductSpace.rclikeToReal ℂ E`, but this
-- instance may be not definitionally equal to some other “natural” instance. So, we assume
-- `[NormedSpace ℝ E]`.
-- -/
-- theorem _root_.isBoundedBilinearMap_inner [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] :
--     IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
--   { add_left := inner_add_left
--     smul_left := fun r x y => by
--       simp only [← algebraMap_smul ℂ r x, algebraMap_eq_ofReal, inner_smul_real_left]
--     add_right := inner_add_right
--     smul_right := fun r x y => by
--       simp only [← algebraMap_smul ℂ r y, algebraMap_eq_ofReal, inner_smul_real_right]
--     bound :=
--       ⟨1, zero_lt_one, fun x y => by
--         rw [one_mul]
--         exact norm_inner_le_norm x y⟩ }

end Norm_Seminormed

section Norm

open scoped InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace E]
variable {ι : Type*} {ι' : Type*} {ι'' : Type*}

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : ℂ} (hx : x ≠ 0)
    (hr : r ≠ 0) : ‖⟪x, r • x⟫‖ / (‖x‖ * ‖r • x‖) = 1 := by
  have hx' : ‖x‖ ≠ 0 := by simp [hx]
  have hr' : ‖r‖ ≠ 0 := by simp [hr]
  rw [inner_smul_right, norm_mul, ← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm, norm_smul]
  rw [← mul_assoc, ← div_div, mul_div_cancel_right₀ _ hx', ← div_div, mul_comm,
    mul_div_cancel_right₀ _ hr', div_self hx']

-- theorem norm_inner_eq_norm_tfae (x y : E) :
--     List.TFAE [‖⟪x, y⟫‖ = ‖x‖ * ‖y‖,
--       x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫) • x,
--       x = 0 ∨ ∃ r : ℂ, y = r • x,
--       x = 0 ∨ y ∈ ℂ ∙ x] := by
--   tfae_have 1 → 2 := by
--     refine fun h => or_iff_not_imp_left.2 fun hx₀ => ?_
--     have : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hx₀)
--     rw [← sq_eq_sq, mul_pow, ← mul_right_inj' this, eq_comm, ← sub_eq_zero, ← mul_sub] at h <;>
--       try positivity
--     simp only [@norm_sq_eq_inner] at h
--     letI : InnerProductSpace.Core E := InnerProductSpace.toCore
--     erw [← InnerProductSpace.Core.cauchy_schwarz_aux, InnerProductSpace.Core.normSq_eq_zero,
--       sub_eq_zero] at h
--     rw [div_eq_inv_mul, mul_smul, h, inv_smul_smul₀]
--     rwa [inner_self_ne_zero]
--   tfae_have 2 → 3 := fun h => h.imp_right fun h' => ⟨_, h'⟩
--   tfae_have 3 → 1 := by
--     rintro (rfl | ⟨r, rfl⟩) <;>
--     simp [inner_smul_right, norm_smul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_mul_norm,
--       sq, mul_left_comm]
--   tfae_have 3 ↔ 4 := by simp only [Submodule.mem_span_singleton, eq_comm]
--   tfae_finish

-- /-- If the inner product of two vectors is equal to the product of their norms, then the two
-- vectors
-- are multiples of each other. One form of the equality case for Cauchy-Schwarz.
-- Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
-- theorem norm_inner_eq_norm_iff {x y : E} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
--     ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ ∃ r : ℂ, r ≠ 0 ∧ y = r • x :=
--   calc
--     ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ r : ℂ, y = r • x :=
--       (@norm_inner_eq_norm_tfae _ _ _ x y).out 0 2
--     _ ↔ ∃ r : ℂ, y = r • x := or_iff_right hx₀
--     _ ↔ ∃ r : ℂ, r ≠ 0 ∧ y = r • x :=
--       ⟨fun ⟨r, h⟩ => ⟨r, fun hr₀ => hy₀ <| h.symm ▸ smul_eq_zero.2 <| Or.inl hr₀, h⟩,
--         fun ⟨r, _hr₀, h⟩ => ⟨r, h⟩⟩

-- /-- The inner product of two vectors, divided by the product of their
-- norms, has absolute value 1 if and only if they are nonzero and one is
-- a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
-- theorem norm_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
--     ‖⟪x, y⟫ / (‖x‖ * ‖y‖)‖ = 1 ↔ x ≠ 0 ∧ ∃ r : ℂ, r ≠ 0 ∧ y = r • x := by
--   constructor
--   · intro h
--     have hx₀ : x ≠ 0 := fun h₀ => by simp [h₀] at h
--     have hy₀ : y ≠ 0 := fun h₀ => by simp [h₀] at h
--     refine ⟨hx₀, (norm_inner_eq_norm_iff hx₀ hy₀).1 <| eq_of_div_eq_one ?_⟩
--     simpa using h
--   · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
--     simp only [norm_div, norm_mul, norm_ofReal, abs_norm]
--     exact norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

-- theorem inner_eq_norm_mul_iff_div {x y : E} (h₀ : x ≠ 0) :
--     ⟪x, y⟫ = (‖x‖ : ℂ) * ‖y‖ ↔ (‖y‖ / ‖x‖ : ℂ) • x = y := by
--   have h₀' := h₀
--   rw [← norm_ne_zero_iff, Ne, ← @ofReal_eq_zero ℂ] at h₀'
--   constructor <;> intro h
--   · have : x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫ : ℂ) • x :=
--       ((@norm_inner_eq_norm_tfae _ _ _ x y).out 0 1).1 (by simp [h])
--     rw [this.resolve_left h₀, h]
--     simp [norm_smul, inner_self_ofReal_norm, mul_div_cancel_right₀ _ h₀']
--   · conv_lhs => rw [← h, inner_smul_right, inner_self_eq_norm_sq_to_K]
--     field_simp [sq, mul_left_comm]

-- /-- If the inner product of two vectors is equal to the product of their norms (i.e.,
-- `⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
-- of the equality case for Cauchy-Schwarz.
-- Compare `norm_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
-- theorem inner_eq_norm_mul_iff {x y : E} :
--     ⟪x, y⟫ = (‖x‖ : ℂ) * ‖y‖ ↔ (‖y‖ : ℂ) • x = (‖x‖ : ℂ) • y := by
--   rcases eq_or_ne x 0 with (rfl | h₀)
--   · simp
--   · rw [inner_eq_norm_mul_iff_div h₀, div_eq_inv_mul, mul_smul, inv_smul_eq_iff₀]
--     rwa [Ne, ofReal_eq_zero, norm_eq_zero]

-- /-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
-- the equality case for Cauchy-Schwarz. -/
-- theorem inner_eq_one_iff_of_norm_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
--     ⟪x, y⟫ = 1 ↔ x = y := by
--   convert inner_eq_norm_mul_iff (E := E) using 2 <;> simp [hx, hy]

-- /-- The sphere of radius `r = ‖y‖` is tangent to the plane `⟪x, y⟫ = ‖y‖ ^ 2` at `x = y`. -/
-- theorem eq_of_norm_le_re_inner_eq_norm_sq {x y : E} (hle : ‖x‖ ≤ ‖y‖) (h : re ⟪x, y⟫ = ‖y‖ ^ 2) :
--     x = y := by
--   suffices H : re ⟪x - y, x - y⟫ ≤ 0 by rwa [inner_self_nonpos, sub_eq_zero] at H
--   have H₁ : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
--   have H₂ : re ⟪y, x⟫ = ‖y‖ ^ 2 := by rwa [← inner_conj_symm, conj_re]
--   simpa [inner_sub_left, inner_sub_right, ← norm_sq_eq_inner, h, H₂] using H₁

end Norm

section BesselsInequality

variable [SeminormedAddCommGroup E] [InnerProductSpace E]

variable {ι : Type*} (x : E) {v : ι → E}

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

/-- Bessel's inequality for finite sums. -/
theorem Orthonormal.sum_inner_products_le {s : Finset ι} (hv : Orthonormal v) :
    ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h₂ :
    (∑ i ∈ s, ∑ j ∈ s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫) = (∑ k ∈ s, ⟪v k, x⟫ * ⟪x, v k⟫ : ℂ) := by
    classical exact hv.inner_left_right_finset
  have h₃ : ∀ z : ℂ, re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [mul_conj, normSq_eq_def']
    norm_cast
  suffices hbf : ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ ^ 2 = ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 by
    rw [← sub_nonneg, ← hbf]
    simp only [norm_nonneg, pow_nonneg]
  rw [@norm_sub_sq, sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_inner, inner_sum, sum_inner]
  simp only [inner_smul_right, two_mul, inner_smul_left, inner_conj_symm, ← mul_assoc, h₂,
    add_sub_cancel_right, sub_right_inj]
  simp only [map_sum, ← inner_conj_symm x, ← h₃]

/-- Bessel's inequality. -/
theorem Orthonormal.tsum_inner_products_le (hv : Orthonormal v) :
    ∑' i, ‖⟪v i, x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  refine tsum_le_of_sum_le' ?_ fun s => hv.sum_inner_products_le x
  simp only [norm_nonneg, pow_nonneg]

/-- The sum defined in Bessel's inequality is summable. -/
theorem Orthonormal.inner_products_summable (hv : Orthonormal v) :
    Summable fun i => ‖⟪v i, x⟫‖ ^ 2 := by
  use ⨆ s : Finset ι, ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    simp only [norm_nonneg, pow_nonneg]
  · refine isLUB_ciSup ?_
    use ‖x‖ ^ 2
    rintro y ⟨s, rfl⟩
    exact hv.sum_inner_products_le x

end BesselsInequality

section RCLike

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

/-- A field `ℂ` satisfying `RCLike` is itself a `ℂ`-inner product space. -/
instance RCLike.innerProductSpace : InnerProductSpace ℂ where
  inner x y := conj x * y
  norm_sq_eq_inner x := by simp only [inner, conj_mul, ← ofReal_pow, ofReal_re]
  conj_symm x y := by simp only [mul_comm, map_mul, starRingEnd_self_apply]
  add_left x y z := by simp only [add_mul, map_add]
  smul_left x y z := by simp only [mul_assoc, smul_eq_mul, map_mul]

@[simp]
theorem RCLike.inner_apply (x y : ℂ) : ⟪x, y⟫ = conj x * y :=
  rfl

end RCLike

section Submodule

variable [SeminormedAddCommGroup E] [InnerProductSpace E]

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

/-! ### Inner product space structure on subspaces -/

/-- Induced inner product on a submodule. -/
instance Submodule.innerProductSpace (W : Submodule ℂ E) : InnerProductSpace W :=
  { Submodule.normedSpace W with
    inner := fun x y => ⟪(x : E), (y : E)⟫
    conj_symm := fun _ _ => inner_conj_symm _ _
    norm_sq_eq_inner := fun x => norm_sq_eq_inner (x : E)
    add_left := fun _ _ _ => inner_add_left _ _ _
    smul_left := fun _ _ _ => inner_smul_left _ _ _ }

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp]
theorem Submodule.coe_inner (W : Submodule ℂ E) (x y : W) : ⟪x, y⟫ = ⟪(x : E), ↑y⟫ :=
  rfl

theorem Orthonormal.codRestrict {ι : Type*} {v : ι → E} (hv : Orthonormal v) (s : Submodule ℂ E)
    (hvs : ∀ i, v i ∈ s) : @Orthonormal s _ _ ι (Set.codRestrict v s hvs) :=
  s.subtypeₗᵢ.orthonormal_comp_iff.mp hv

theorem orthonormal_span {ι : Type*} {v : ι → E} (hv : Orthonormal v) :
    @Orthonormal (Submodule.span ℂ (Set.range v)) _ _ ι fun i : ι =>
      ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ :=
  hv.codRestrict (Submodule.span ℂ (Set.range v)) fun i =>
    Submodule.subset_span (Set.mem_range_self i)

end Submodule

/-! ### Families of mutually-orthogonal subspaces of an inner product space -/

section OrthogonalFamily_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace E]

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

variable {ι : Type*}

open DirectSum

/-- An indexed family of mutually-orthogonal subspaces of an inner product space `E`.

The simple way to express this concept would be as a condition on `V : ι → Submodule ℂ E`.  We
instead implement it as a condition on a family of inner product spaces each equipped with an
isometric embedding into `E`, thus making it a property of morphisms rather than subobjects.
The connection to the subobject spelling is shown in `orthogonalFamily_iff_pairwise`.

This definition is less lightweight, but allows for better definitional properties when the inner
product space structure on each of the submodules is important -- for example, when considering
their Hilbert sum (`PiLp V 2`).  For example, given an orthonormal set of vectors `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, which it is convenient
to be able to discuss using `ι → ℂ` rather than `Π i : ι, span ℂ (v i)`. -/
def OrthogonalFamily (G : ι → Type*) [∀ i, SeminormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace (G i)] (V : ∀ i, G i →ₗᵢ[ℂ] E) : Prop :=
  Pairwise fun i j => ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0

variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace (G i)]
  {V : ∀ i, G i →ₗᵢ[ℂ] E}

theorem Orthonormal.orthogonalFamily {v : ι → E} (hv : Orthonormal v) :
    OrthogonalFamily (fun _i : ι => ℂ) fun i => LinearIsometry.toSpanSingleton ℂ E (hv.1 i) :=
  fun i j hij a b => by simp [inner_smul_left, inner_smul_right, hv.2 hij]

section
variable (hV : OrthogonalFamily G V)
include hV

theorem OrthogonalFamily.eq_ite [DecidableEq ι] {i j : ι} (v : G i) (w : G j) :
    ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0 := by
  split_ifs with h
  · rfl
  · exact hV h v w

theorem OrthogonalFamily.inner_right_dfinsupp
    [∀ (i) (x : G i), Decidable (x ≠ 0)] [DecidableEq ι] (l : ⨁ i, G i) (i : ι) (v : G i) :
    ⟪V i v, l.sum fun j => V j⟫ = ⟪v, l i⟫ :=
  calc
    ⟪V i v, l.sum fun j => V j⟫ = l.sum fun j => fun w => ⟪V i v, V j w⟫ :=
      DFinsupp.inner_sum (fun j => V j) l (V i v)
    _ = l.sum fun j => fun w => ite (i = j) ⟪V i v, V j w⟫ 0 :=
      (congr_arg l.sum <| funext fun j => funext <| hV.eq_ite v)
    _ = ⟪v, l i⟫ := by
      simp only [DFinsupp.sum, Submodule.coe_inner, Finset.sum_ite_eq, ite_eq_left_iff,
        DFinsupp.mem_support_toFun]
      split_ifs with h
      · simp only [LinearIsometry.inner_map_map]
      · simp only [of_not_not h, inner_zero_right]

theorem OrthogonalFamily.inner_right_fintype [Fintype ι] (l : ∀ i, G i) (i : ι) (v : G i) :
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫ := by
  classical
  calc
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ∑ j : ι, ⟪V i v, V j (l j)⟫ := by rw [inner_sum]
    _ = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :=
      (congr_arg (Finset.sum Finset.univ) <| funext fun j => hV.eq_ite v (l j))
    _ = ⟪v, l i⟫ := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, (V i).inner_map_map, if_true]

nonrec theorem OrthogonalFamily.inner_sum (l₁ l₂ : ∀ i, G i) (s : Finset ι) :
    ⟪∑ i ∈ s, V i (l₁ i), ∑ j ∈ s, V j (l₂ j)⟫ = ∑ i ∈ s, ⟪l₁ i, l₂ i⟫ := by
  classical
  calc
    ⟪∑ i ∈ s, V i (l₁ i), ∑ j ∈ s, V j (l₂ j)⟫ = ∑ j ∈ s, ∑ i ∈ s, ⟪V i (l₁ i), V j (l₂ j)⟫ := by
      simp only [sum_inner, inner_sum]
    _ = ∑ j ∈ s, ∑ i ∈ s, ite (i = j) ⟪V i (l₁ i), V j (l₂ j)⟫ 0 := by
      congr with i
      congr with j
      apply hV.eq_ite
    _ = ∑ i ∈ s, ⟪l₁ i, l₂ i⟫ := by
      simp only [Finset.sum_ite_of_true, Finset.sum_ite_eq', LinearIsometry.inner_map_map,
        imp_self, imp_true_iff]

theorem OrthogonalFamily.norm_sum (l : ∀ i, G i) (s : Finset ι) :
    ‖∑ i ∈ s, V i (l i)‖ ^ 2 = ∑ i ∈ s, ‖l i‖ ^ 2 := by
  have : ((‖∑ i ∈ s, V i (l i)‖ : ℝ) : ℂ) ^ 2 = ∑ i ∈ s, ((‖l i‖ : ℝ) : ℂ) ^ 2 := by
    simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum]
  exact mod_cast this

/-- The composition of an orthogonal family of subspaces with an injective function is also an
orthogonal family. -/
theorem OrthogonalFamily.comp {γ : Type*} {f : γ → ι} (hf : Function.Injective f) :
    OrthogonalFamily (fun g => G (f g)) fun g => V (f g) :=
  fun _i _j hij v w => hV (hf.ne hij) v w

theorem OrthogonalFamily.orthonormal_sigma_orthonormal {α : ι → Type*} {v_family : ∀ i, α i → G i}
    (hv_family : ∀ i, Orthonormal (v_family i)) :
    Orthonormal fun a : Σi, α i => V a.1 (v_family a.1 a.2) := by
  constructor
  · rintro ⟨i, v⟩
    simpa only [LinearIsometry.norm_map] using (hv_family i).left v
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  by_cases hij : i = j
  · subst hij
    have : v ≠ w := fun h => by
      subst h
      exact hvw rfl
    simpa only [LinearIsometry.inner_map_map] using (hv_family i).2 this
  · exact hV hij (v_family i v) (v_family j w)

theorem OrthogonalFamily.norm_sq_diff_sum [DecidableEq ι] (f : ∀ i, G i) (s₁ s₂ : Finset ι) :
    ‖(∑ i ∈ s₁, V i (f i)) - ∑ i ∈ s₂, V i (f i)‖ ^ 2 =
      (∑ i ∈ s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖f i‖ ^ 2 := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  let F : ∀ i, G i := fun i => if i ∈ s₁ then f i else -f i
  have hF₁ : ∀ i ∈ s₁ \ s₂, F i = f i := fun i hi => if_pos (Finset.sdiff_subset hi)
  have hF₂ : ∀ i ∈ s₂ \ s₁, F i = -f i := fun i hi => if_neg (Finset.mem_sdiff.mp hi).2
  have hF : ∀ i, ‖F i‖ = ‖f i‖ := by
    intro i
    dsimp only [F]
    split_ifs <;> simp only [eq_self_iff_true, norm_neg]
  have :
    ‖(∑ i ∈ s₁ \ s₂, V i (F i)) + ∑ i ∈ s₂ \ s₁, V i (F i)‖ ^ 2 =
      (∑ i ∈ s₁ \ s₂, ‖F i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖F i‖ ^ 2 := by
    have hs : Disjoint (s₁ \ s₂) (s₂ \ s₁) := disjoint_sdiff_sdiff
    simpa only [Finset.sum_union hs] using hV.norm_sum F (s₁ \ s₂ ∪ s₂ \ s₁)
  convert this using 4
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hF₁ i hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hF₂ i hi, LinearIsometry.map_neg]
  · simp only [hF]
  · simp only [hF]

/-- A family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(fun i ↦ ‖f i‖ ^ 2)` is summable. -/
theorem OrthogonalFamily.summable_iff_norm_sq_summable [CompleteSpace E] (f : ∀ i, G i) :
    (Summable fun i => V i (f i)) ↔ Summable fun i => ‖f i‖ ^ 2 := by
  classical
    simp only [summable_iff_cauchySeq_finset, NormedAddCommGroup.cauchySeq_iff, Real.norm_eq_abs]
    constructor
    · intro hf ε hε
      obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε)
      use a
      intro s₁ hs₁ s₂ hs₂
      rw [← Finset.sum_sdiff_sub_sum_sdiff]
      refine (abs_sub _ _).trans_lt ?_
      have : ∀ i, 0 ≤ ‖f i‖ ^ 2 := fun i : ι => sq_nonneg _
      simp only [Finset.abs_sum_of_nonneg' this]
      have : ((∑ i ∈ s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖f i‖ ^ 2) < √ε ^ 2 := by
        rw [← hV.norm_sq_diff_sum, sq_lt_sq, abs_of_nonneg (sqrt_nonneg _),
          abs_of_nonneg (norm_nonneg _)]
        exact H s₁ hs₁ s₂ hs₂
      have hη := sq_sqrt (le_of_lt hε)
      linarith
    · intro hf ε hε
      have hε' : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε)
      obtain ⟨a, H⟩ := hf _ hε'
      use a
      intro s₁ hs₁ s₂ hs₂
      refine (abs_lt_of_sq_lt_sq' ?_ (le_of_lt hε)).2
      have has : a ≤ s₁ ⊓ s₂ := le_inf hs₁ hs₂
      rw [hV.norm_sq_diff_sum]
      have Hs₁ : ∑ x ∈ s₁ \ s₂, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
        convert H _ hs₁ _ has
        have : s₁ ⊓ s₂ ⊆ s₁ := Finset.inter_subset_left
        rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      have Hs₂ : ∑ x ∈ s₂ \ s₁, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
        convert H _ hs₂ _ has
        have : s₁ ⊓ s₂ ⊆ s₂ := Finset.inter_subset_right
        rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      linarith

end

end OrthogonalFamily_Seminormed

section OrthogonalFamily

variable [NormedAddCommGroup E] [InnerProductSpace E]

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

variable {ι : Type*}
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace (G i)]
  {V : ∀ i, G i →ₗᵢ[ℂ] E} (hV : OrthogonalFamily G V) [dec_V : ∀ (i) (x : G i), Decidable (x ≠ 0)]

/-- An orthogonal family forms an independent family of subspaces; that is, any collection of
elements each from a different subspace in the family is linearly independent. In particular, the
pairwise intersections of elements of the family are 0. -/
theorem OrthogonalFamily.independent {V : ι → Submodule ℂ E}
    (hV : OrthogonalFamily (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    CompleteLattice.Independent V := by
  classical
  apply CompleteLattice.independent_of_dfinsupp_lsum_injective
  refine LinearMap.ker_eq_bot.mp ?_
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  ext i
  suffices ⟪(v i : E), v i⟫ = 0 by simpa only [inner_self_eq_zero] using this
  calc
    ⟪(v i : E), v i⟫ = ⟪(v i : E), DFinsupp.lsum ℕ (fun i => (V i).subtype) v⟫ := by
      simpa only [DFinsupp.sumAddHom_apply, DFinsupp.lsum_apply_apply] using
        (hV.inner_right_dfinsupp v i (v i)).symm
    _ = 0 := by simp only [hv, inner_zero_right]

theorem DirectSum.IsInternal.collectedBasis_orthonormal [DecidableEq ι] {V : ι → Submodule ℂ E}
    (hV : OrthogonalFamily (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (hV_sum : DirectSum.IsInternal fun i => V i) {α : ι → Type*}
    {v_family : ∀ i, Basis (α i) ℂ (V i)} (hv_family : ∀ i, Orthonormal (v_family i)) :
    Orthonormal (hV_sum.collectedBasis v_family) := by
  simpa only [hV_sum.collectedBasis_coe] using hV.orthonormal_sigma_orthonormal hv_family

end OrthogonalFamily

section Continuous

variable [SeminormedAddCommGroup E] [InnerProductSpace E]

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

/-!
### Continuity of the inner product
-/


theorem continuous_inner : Continuous fun p : E × E => ⟪p.1, p.2⟫ :=
  sorry
  -- letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  -- letI : IsScalarTower ℝ ℂ E := RestrictScalars.isScalarTower _ _ _
  -- isBoundedBilinearMap_inner.continuous

variable {α : Type*}

theorem Filter.Tendsto.inner {f g : α → E} {l : Filter α} {x y : E} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
  (continuous_inner.tendsto _).comp (hf.prod_mk_nhds hg)

variable [TopologicalSpace α] {f g : α → E} {x : α} {s : Set α}

theorem ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x :=
  Filter.Tendsto.inner hf hg

theorem ContinuousAt.inner (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun t => ⟪f t, g t⟫) x :=
  Filter.Tendsto.inner hf hg

theorem ContinuousOn.inner (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun t => ⟪f t, g t⟫) s := fun x hx => (hf x hx).inner (hg x hx)

@[continuity]
theorem Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun t => ⟪f t, g t⟫ :=
  continuous_iff_continuousAt.2 fun _x => hf.continuousAt.inner hg.continuousAt

end Continuous

section ReApplyInnerSelf

variable [SeminormedAddCommGroup E] [InnerProductSpace E]

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

/-- Extract a real bilinear form from an operator `T`,
by taking the pairing `fun x ↦ re ⟪T x, x⟫`. -/
def ContinuousLinearMap.reApplyInnerSelf (T : E →L[ℂ] E) (x : E) : ℝ :=
  re ⟪T x, x⟫

theorem ContinuousLinearMap.reApplyInnerSelf_apply (T : E →L[ℂ] E) (x : E) :
    T.reApplyInnerSelf x = re ⟪T x, x⟫ :=
  rfl

end ReApplyInnerSelf

section ReApplyInnerSelf_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace E]

local notation "⟪" x ", " y "⟫" => @inner _ _ x y

local notation "IK" => @RCLike.I ℂ _

local postfix:90 "†" => starRingEnd _

theorem ContinuousLinearMap.reApplyInnerSelf_continuous (T : E →L[ℂ] E) :
    Continuous T.reApplyInnerSelf :=
  reCLM.continuous.comp <| T.continuous.inner continuous_id

theorem ContinuousLinearMap.reApplyInnerSelf_smul (T : E →L[ℂ] E) (x : E) {c : ℂ} :
    T.reApplyInnerSelf (c • x) = ‖c‖ ^ 2 * T.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.reApplyInnerSelf_apply,
    inner_smul_left, inner_smul_right, ← mul_assoc, mul_conj, ← ofReal_pow, ← smul_re,
    Algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebraMap_eq_ofReal]

end ReApplyInnerSelf_Seminormed

set_option linter.style.longFile 2500
