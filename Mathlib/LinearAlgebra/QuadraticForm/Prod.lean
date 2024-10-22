/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-! # Quadratic form on product and pi types

## Main definitions

* `QuadraticForm.prod Q₁ Q₂`: the quadratic form constructed elementwise on a product
* `QuadraticForm.pi Q`: the quadratic form constructed elementwise on a pi type

## Main results

* `QuadraticForm.Equivalent.prod`, `QuadraticForm.Equivalent.pi`: quadratic forms are equivalent
  if their components are equivalent
* `QuadraticForm.nonneg_prod_iff`, `QuadraticForm.nonneg_pi_iff`: quadratic forms are positive-
  semidefinite if and only if their components are positive-semidefinite.
* `QuadraticForm.posDef_prod_iff`, `QuadraticForm.posDef_pi_iff`: quadratic forms are positive-
  definite if and only if their components are positive-definite.

## Implementation notes

Many of the lemmas in this file could be generalized into results about sums of positive and
non-negative elements, and would generalize to any map `Q` where `Q 0 = 0`, not just quadratic
forms specifically.

-/


universe u v w

variable {ι : Type*} {R : Type*} {M₁ M₂ N₁ N₂ P : Type*} {Mᵢ Nᵢ : ι → Type*}


namespace QuadraticMap

open QuadraticMap

section Prod

section Semiring
variable [CommSemiring R]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
variable [AddCommMonoid P]
variable [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂] [Module R P]

/-- Construct a quadratic form on a product of two modules from the quadratic form on each module.
-/
@[simps!]
def prod (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) : QuadraticMap R (M₁ × M₂) P :=
  Q₁.comp (LinearMap.fst _ _ _) + Q₂.comp (LinearMap.snd _ _ _)

/-- An isometry between quadratic forms generated by `QuadraticForm.prod` can be constructed
from a pair of isometries between the left and right parts. -/
@[simps toLinearEquiv]
def IsometryEquiv.prod
    {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P}
    {Q₁' : QuadraticMap R N₁ P} {Q₂' : QuadraticMap R N₂ P}
    (e₁ : Q₁.IsometryEquiv Q₁') (e₂ : Q₂.IsometryEquiv Q₂') :
    (Q₁.prod Q₂).IsometryEquiv (Q₁'.prod Q₂') where
  map_app' x := congr_arg₂ (· + ·) (e₁.map_app x.1) (e₂.map_app x.2)
  toLinearEquiv := LinearEquiv.prod e₁.toLinearEquiv e₂.toLinearEquiv

/-- `LinearMap.inl` as an isometry. -/
@[simps!]
def Isometry.inl (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) : Q₁ →qᵢ (Q₁.prod Q₂) where
  toLinearMap := LinearMap.inl R _ _
  map_app' m₁ := by simp

/-- `LinearMap.inr` as an isometry. -/
@[simps!]
def Isometry.inr (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) : Q₂ →qᵢ (Q₁.prod Q₂) where
  toLinearMap := LinearMap.inr R _ _
  map_app' m₁ := by simp

variable (M₂) in
/-- `LinearMap.fst` as an isometry, when the second space has the zero quadratic form. -/
@[simps!]
def Isometry.fst (Q₁ : QuadraticMap R M₁ P) : (Q₁.prod (0 : QuadraticMap R M₂ P)) →qᵢ Q₁ where
  toLinearMap := LinearMap.fst R _ _
  map_app' m₁ := by simp

variable (M₁) in
/-- `LinearMap.snd` as an isometry, when the first space has the zero quadratic form. -/
@[simps!]
def Isometry.snd (Q₂ : QuadraticMap R M₂ P) : ((0 : QuadraticMap R M₁ P).prod Q₂) →qᵢ Q₂ where
  toLinearMap := LinearMap.snd R _ _
  map_app' m₁ := by simp

@[simp]
lemma Isometry.fst_comp_inl (Q₁ : QuadraticMap R M₁ P) :
    (fst M₂ Q₁).comp (inl Q₁ (0 : QuadraticMap R M₂ P)) = .id _ :=
  ext fun _ => rfl

@[simp]
lemma Isometry.snd_comp_inr (Q₂ : QuadraticMap R M₂ P) :
    (snd M₁ Q₂).comp (inr (0 : QuadraticMap R M₁ P) Q₂) = .id _ :=
  ext fun _ => rfl

@[simp]
lemma Isometry.snd_comp_inl (Q₂ : QuadraticMap R M₂ P) :
    (snd M₁ Q₂).comp (inl (0 : QuadraticMap R M₁ P) Q₂) = 0 :=
  ext fun _ => rfl

@[simp]
lemma Isometry.fst_comp_inr (Q₁ : QuadraticMap R M₁ P) :
    (fst M₂ Q₁).comp (inr Q₁ (0 : QuadraticMap R M₂ P)) = 0 :=
  ext fun _ => rfl

theorem Equivalent.prod {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P}
    {Q₁' : QuadraticMap R N₁ P} {Q₂' : QuadraticMap R N₂ P} (e₁ : Q₁.Equivalent Q₁')
    (e₂ : Q₂.Equivalent Q₂') : (Q₁.prod Q₂).Equivalent (Q₁'.prod Q₂') :=
  Nonempty.map2 IsometryEquiv.prod e₁ e₂

/-- `LinearEquiv.prodComm` is isometric. -/
@[simps!]
def IsometryEquiv.prodComm (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) :
    (Q₁.prod Q₂).IsometryEquiv (Q₂.prod Q₁) where
  toLinearEquiv := LinearEquiv.prodComm _ _ _
  map_app' _ := add_comm _ _

/-- `LinearEquiv.prodProdProdComm` is isometric. -/
@[simps!]
def IsometryEquiv.prodProdProdComm
    (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P)
    (Q₃ : QuadraticMap R N₁ P) (Q₄ : QuadraticMap R N₂ P) :
    ((Q₁.prod Q₂).prod (Q₃.prod Q₄)).IsometryEquiv ((Q₁.prod Q₃).prod (Q₂.prod Q₄)) where
  toLinearEquiv := LinearEquiv.prodProdProdComm _ _ _ _ _
  map_app' _ := add_add_add_comm _ _ _ _

/-- If a product is anisotropic then its components must be. The converse is not true. -/
theorem anisotropic_of_prod
    {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} (h : (Q₁.prod Q₂).Anisotropic) :
    Q₁.Anisotropic ∧ Q₂.Anisotropic := by
  simp_rw [Anisotropic, prod_apply, Prod.forall, Prod.mk_eq_zero] at h
  constructor
  · intro x hx
    refine (h x 0 ?_).1
    rw [hx, zero_add, map_zero]
  · intro x hx
    refine (h 0 x ?_).2
    rw [hx, add_zero, map_zero]

theorem nonneg_prod_iff [Preorder P] [CovariantClass P P (· + ·) (· ≤ ·)]
    {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} :
    (∀ x, 0 ≤ (Q₁.prod Q₂) x) ↔ (∀ x, 0 ≤ Q₁ x) ∧ ∀ x, 0 ≤ Q₂ x := by
  simp_rw [Prod.forall, prod_apply]
  constructor
  · intro h
    constructor
    · intro x; simpa only [add_zero, map_zero] using h x 0
    · intro x; simpa only [zero_add, map_zero] using h 0 x
  · rintro ⟨h₁, h₂⟩ x₁ x₂
    exact add_nonneg (h₁ x₁) (h₂ x₂)

theorem posDef_prod_iff [PartialOrder P] [CovariantClass P P (· + ·) (· ≤ ·)]
    {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} :
    (Q₁.prod Q₂).PosDef ↔ Q₁.PosDef ∧ Q₂.PosDef := by
  simp_rw [posDef_iff_nonneg, nonneg_prod_iff]
  constructor
  · rintro ⟨⟨hle₁, hle₂⟩, ha⟩
    obtain ⟨ha₁, ha₂⟩ := anisotropic_of_prod ha
    exact ⟨⟨hle₁, ha₁⟩, ⟨hle₂, ha₂⟩⟩
  · rintro ⟨⟨hle₁, ha₁⟩, ⟨hle₂, ha₂⟩⟩
    refine ⟨⟨hle₁, hle₂⟩, ?_⟩
    rintro ⟨x₁, x₂⟩ (hx : Q₁ x₁ + Q₂ x₂ = 0)
    rw [add_eq_zero_iff_of_nonneg (hle₁ x₁) (hle₂ x₂), ha₁.eq_zero_iff, ha₂.eq_zero_iff] at hx
    rwa [Prod.mk_eq_zero]

theorem PosDef.prod [PartialOrder P] [CovariantClass P P (· + ·) (· ≤ ·)]
    {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} (h₁ : Q₁.PosDef) (h₂ : Q₂.PosDef) :
    (Q₁.prod Q₂).PosDef :=
  posDef_prod_iff.mpr ⟨h₁, h₂⟩

theorem IsOrtho.prod {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P}
    {v w : M₁ × M₂} (h₁ : Q₁.IsOrtho v.1 w.1) (h₂ : Q₂.IsOrtho v.2 w.2) :
    (Q₁.prod Q₂).IsOrtho v w :=
  (congr_arg₂ HAdd.hAdd h₁ h₂).trans <| add_add_add_comm _ _ _ _

@[simp] theorem IsOrtho.inl_inr {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P}
    (m₁ : M₁) (m₂ : M₂) :
    (Q₁.prod Q₂).IsOrtho (m₁, 0) (0, m₂) :=
      QuadraticMap.IsOrtho.prod (.zero_right _) (.zero_left _)

@[simp] theorem IsOrtho.inr_inl {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P}
    (m₁ : M₁) (m₂ : M₂) :
    (Q₁.prod Q₂).IsOrtho (0, m₂) (m₁, 0) := (IsOrtho.inl_inr _ _).symm

@[simp] theorem isOrtho_inl_inl_iff {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P}
    (m₁ m₁' : M₁) :
    (Q₁.prod Q₂).IsOrtho (m₁, 0) (m₁', 0) ↔ Q₁.IsOrtho m₁ m₁' := by
  simp [isOrtho_def]

@[simp] theorem isOrtho_inr_inr_iff {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P}
    (m₂ m₂' : M₂) :
    (Q₁.prod Q₂).IsOrtho (0, m₂) (0, m₂') ↔ Q₂.IsOrtho m₂ m₂' := by
  simp [isOrtho_def]

end Semiring

section Ring

variable [CommRing R]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup P]
variable [Module R M₁] [Module R M₂] [Module R P]

@[simp] theorem polar_prod (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) (x y : M₁ × M₂) :
    polar (Q₁.prod Q₂) x y = polar Q₁ x.1 y.1 + polar Q₂ x.2 y.2 := by
  dsimp [polar]
  abel

@[simp] theorem polarBilin_prod (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) :
    (Q₁.prod Q₂).polarBilin =
      Q₁.polarBilin.compl₁₂ (.fst R M₁ M₂) (.fst R M₁ M₂) +
      Q₂.polarBilin.compl₁₂ (.snd R M₁ M₂) (.snd R M₁ M₂) :=
  LinearMap.ext₂ <| polar_prod _ _

@[simp] theorem associated_prod [Invertible (2 : R)]
    (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) :
    associated (Q₁.prod Q₂) =
      (associated Q₁).compl₁₂ (.fst R M₁ M₂) (.fst R M₁ M₂) +
      (associated Q₂).compl₁₂ (.snd R M₁ M₂) (.snd R M₁ M₂) := by
  dsimp [associated, associatedHom]
  rw [polarBilin_prod, smul_add]
  rfl

end Ring

end Prod

section Pi

section Semiring
variable [CommSemiring R]
variable [∀ i, AddCommMonoid (Mᵢ i)] [∀ i, AddCommMonoid (Nᵢ i)] [AddCommMonoid P]
variable [∀ i, Module R (Mᵢ i)] [∀ i, Module R (Nᵢ i)] [Module R P]

/-- Construct a quadratic form on a family of modules from the quadratic form on each module. -/
def pi [Fintype ι] (Q : ∀ i, QuadraticMap R (Mᵢ i) P) : QuadraticMap R (∀ i, Mᵢ i) P :=
  ∑ i, (Q i).comp (LinearMap.proj i : _ →ₗ[R] Mᵢ i)

@[simp]
theorem pi_apply [Fintype ι] (Q : ∀ i, QuadraticMap R (Mᵢ i) P) (x : ∀ i, Mᵢ i) :
    pi Q x = ∑ i, Q i (x i) :=
  sum_apply _ _ _

theorem pi_apply_single [Fintype ι] [DecidableEq ι]
    (Q : ∀ i, QuadraticMap R (Mᵢ i) P) (i : ι) (m : Mᵢ i) :
    pi Q (Pi.single i m) = Q i m := by
  rw [pi_apply, Fintype.sum_eq_single i fun j hj => ?_, Pi.single_eq_same]
  rw [Pi.single_eq_of_ne hj, map_zero]

/-- An isometry between quadratic forms generated by `QuadraticMap.pi` can be constructed
from a pair of isometries between the left and right parts. -/
@[simps toLinearEquiv]
def IsometryEquiv.pi [Fintype ι]
    {Q : ∀ i, QuadraticMap R (Mᵢ i) P} {Q' : ∀ i, QuadraticMap R (Nᵢ i) P}
    (e : ∀ i, (Q i).IsometryEquiv (Q' i)) : (pi Q).IsometryEquiv (pi Q') where
  map_app' x := by
    simp only [pi_apply, LinearEquiv.piCongrRight, LinearEquiv.toFun_eq_coe,
      IsometryEquiv.coe_toLinearEquiv, IsometryEquiv.map_app]
  toLinearEquiv := LinearEquiv.piCongrRight fun i => (e i : Mᵢ i ≃ₗ[R] Nᵢ i)

/-- `LinearMap.single` as an isometry. -/
@[simps!]
def Isometry.single [Fintype ι] [DecidableEq ι] (Q : ∀ i, QuadraticMap R (Mᵢ i) P) (i : ι) :
    Q i →qᵢ pi Q where
  toLinearMap := LinearMap.single _ _ i
  map_app' := pi_apply_single _ _

/-- `LinearMap.proj` as an isometry, when all but one quadratic form is zero. -/
@[simps!]
def Isometry.proj [Fintype ι] [DecidableEq ι] (i : ι) (Q : QuadraticMap R (Mᵢ i) P) :
    pi (Pi.single i Q) →qᵢ Q where
  toLinearMap := LinearMap.proj i
  map_app' m := by
    dsimp
    rw [pi_apply, Fintype.sum_eq_single i (fun j hij => ?_), Pi.single_eq_same]
    rw [Pi.single_eq_of_ne hij, zero_apply]

/-- Note that `QuadraticMap.Isometry.id` would not be well-typed as the RHS. -/
@[simp, nolint simpNF]  -- ignore the bogus "Left-hand side does not simplify" lint error
theorem Isometry.proj_comp_single_of_same [Fintype ι] [DecidableEq ι]
    (i : ι) (Q : QuadraticMap R (Mᵢ i) P) :
    (proj i Q).comp (single _ i) = .ofEq (Pi.single_eq_same _ _) :=
  ext fun _ => Pi.single_eq_same _ _

/-- Note that `0 : 0 →qᵢ Q` alone would not be well-typed as the RHS. -/
@[simp]
theorem Isometry.proj_comp_single_of_ne [Fintype ι] [DecidableEq ι]
    {i j : ι} (h : i ≠ j) (Q : QuadraticMap R (Mᵢ i) P) :
    (proj i Q).comp (single _ j) = (0 : 0 →qᵢ Q).comp (ofEq (Pi.single_eq_of_ne h.symm _)) :=
  ext fun _ => Pi.single_eq_of_ne h _

theorem Equivalent.pi [Fintype ι] {Q : ∀ i, QuadraticMap R (Mᵢ i) P}
    {Q' : ∀ i, QuadraticMap R (Nᵢ i) P} (e : ∀ i, (Q i).Equivalent (Q' i)) :
    (pi Q).Equivalent (pi Q') :=
  ⟨IsometryEquiv.pi fun i => Classical.choice (e i)⟩

/-- If a family is anisotropic then its components must be. The converse is not true. -/
theorem anisotropic_of_pi [Fintype ι]
    {Q : ∀ i, QuadraticMap R (Mᵢ i) P} (h : (pi Q).Anisotropic) : ∀ i, (Q i).Anisotropic := by
  simp_rw [Anisotropic, pi_apply, funext_iff, Pi.zero_apply] at h
  intro i x hx
  classical
  have := h (Pi.single i x) ?_ i
  · rw [Pi.single_eq_same] at this
    exact this
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j = i
  · subst hji; rw [Pi.single_eq_same, hx]
  · rw [Pi.single_eq_of_ne hji, map_zero]

theorem nonneg_pi_iff {P} [Fintype ι] [OrderedAddCommMonoid P] [Module R P]
    {Q : ∀ i, QuadraticMap R (Mᵢ i) P} : (∀ x, 0 ≤ pi Q x) ↔ ∀ i x, 0 ≤ Q i x := by
  simp_rw [pi, sum_apply, comp_apply, LinearMap.proj_apply]
  constructor
  -- TODO: does this generalize to a useful lemma independent of `QuadraticMap`?
  · intro h i x
    classical
    convert h (Pi.single i x) using 1
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) fun j _ hji => ?_, Pi.single_eq_same]
    rw [Pi.single_eq_of_ne hji, map_zero]
  · rintro h x
    exact Finset.sum_nonneg fun i _ => h i (x i)

theorem posDef_pi_iff {P} [Fintype ι] [OrderedAddCommMonoid P] [Module R P]
    {Q : ∀ i, QuadraticMap R (Mᵢ i) P} : (pi Q).PosDef ↔ ∀ i, (Q i).PosDef := by
  simp_rw [posDef_iff_nonneg, nonneg_pi_iff]
  constructor
  · rintro ⟨hle, ha⟩
    intro i
    exact ⟨hle i, anisotropic_of_pi ha i⟩
  · intro h
    refine ⟨fun i => (h i).1, fun x hx => funext fun i => (h i).2 _ ?_⟩
    rw [pi_apply, Finset.sum_eq_zero_iff_of_nonneg fun j _ => ?_] at hx
    · exact hx _ (Finset.mem_univ _)
    exact (h j).1 _

end Semiring

namespace Ring

variable [CommRing R]
variable [∀ i, AddCommGroup (Mᵢ i)] [∀ i, AddCommGroup (Nᵢ i)] [AddCommGroup P]
variable [∀ i, Module R (Mᵢ i)] [∀ i, Module R (Nᵢ i)] [Module R P]
variable [Fintype ι]

@[simp] theorem polar_pi (Q : ∀ i, QuadraticMap R (Mᵢ i) P) (x y : ∀ i, Mᵢ i) :
    polar (pi Q) x y = ∑ i, polar (Q i) (x i) (y i) := by
  dsimp [polar]
  simp_rw [Finset.sum_sub_distrib, pi_apply, Pi.add_apply]

@[simp] theorem polarBilin_pi (Q : ∀ i, QuadraticMap R (Mᵢ i) P) :
    (pi Q).polarBilin = ∑ i, (Q i).polarBilin.compl₁₂ (.proj i) (.proj i) :=
  LinearMap.ext₂ fun x y => (polar_pi _ _ _).trans <| by simp

@[simp] theorem associated_pi [Invertible (2 : R)] (Q : ∀ i, QuadraticMap R (Mᵢ i) P) :
    associated (pi Q) = ∑ i, (Q i).associated.compl₁₂ (.proj i) (.proj i) := by
  dsimp [associated, associatedHom]
  rw [polarBilin_pi, Finset.smul_sum]
  rfl

end Ring

end Pi

end QuadraticMap
