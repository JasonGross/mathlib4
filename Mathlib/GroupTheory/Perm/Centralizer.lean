/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Perm.ConjAct
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.GroupTheory.Perm.DomMulAct

/-! # Centralizer of a permutation and cardinality of conjugacy classes
  # in the symmetric groups

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `Equiv.Perm α` and `alternatingGroup α`.
Every `g : Equiv.Perm α` has a `cycleType α : Multiset ℕ`.
By `Equiv.Perm.isConj_iff_cycleType_eq`,
two permutations are conjugate in `Equiv.Perm α` iff
their cycle types are equal.
To compute the cardinality of the conjugacy classes, we could use
a purely combinatorial approach and compute the number of permutations
with given cycle type but we resorted to a more algebraic approach.

Given `g : Equiv.Perm α`, the conjugacy class of `g` is the orbit
of `g` under the action `ConjAct (Equiv.Perm α)`, and we use
the orbit-stabilizer theorem
(`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`)
to reduce the computation to the computation of the centralizer of `g`,
the subgroup of `Equiv.Perm α` consisting of all permutations
which commute with `g`. It is accessed here as
`MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`.

We compute this subgroup as follows.

* If `h : MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`, then the action
  of `h` by conjugation on `Equiv.Perm α` stabilizes `g.cycleFactorsFinset`.
  That induces an action of `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  on `g.cycleFactorsFinset` which is defined via
  `Equiv.Perm.OnCycleFactors.subMulActionOnCycleFactors `

* This action defines a group morphism `Equiv.Perm.OnCycleFactors.φ g` from
  `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  to `Equiv.Perm (g.cycleFactorsFinset)`

* `Equiv.Perm.OnCycleFactors.Iφ_eq_range` shows that the range of `Equiv.Perm.OnCycleFactors.φ g`
  is the subgroup `Iφ g` of `Equiv.Perm (g.cycleFactorsFinset)`
  consisting of permutations `τ` which preserve the length of the cycles.
  This is showed by constructing a right inverse `Equiv.Perm.OnCycleFactors.φ'`
  in `Equiv.Perm.OnCycleFactors.hφ'_is_rightInverse`.

* `Equiv.Perm.OnCycleFactors.hφ_range_card` computes the cardinality of
  `range (Equiv.Perm.OnCycleFactors.φ g)` as a product of factorials.

* For an element `z : Equiv.Perm α`, we then prove in
  `Equiv.Perm.OnCycleFactors.hφ_mem_ker_iff` that `ConjAct.toConjAct z` belongs to
  the kernel of `Equiv.Perm.OnCycleFactors.φ g` if and only if it permutes `g.fixedPoints`
  and it acts on each cycle of `g` as a power of that cycle.
  This gives a description of the kernel of `Equiv.Perm.OnCycleFactors.φ g` as the product
  of a symmetric group and of a product of cyclic groups.
  This analysis starts with the morphism `Equiv.Perm.OnCycleFactors.θ`,
  its injectivity `Equiv.Perm.OnCycleFactors.hθ_injective`,
  its range `Equiv.Perm.OnCycleFactors.hφ_ker_eq_θ_range`,
  and  its cardinality `Equiv.Perm.OnCycleFactors.hθ_range_card`.

* `Equiv.Perm.conj_stabilizer_card g` computes the cardinality
  of the centralizer of `g`

* `Equiv.Perm.conj_class_card_mul_eq g` computes the cardinality
  of the conjugacy class of `g`.

* We now can compute the cardinality of the set of permutations with given cycle type.
  The condition for this cardinality to be zero is given by
  `Equiv.Perm.card_of_cycleType_eq_zero_iff`
  which is itself derived from `Equiv.Perm.exists_with_cycleType_iff`.

* `Equiv.Perm.card_of_cycleType_mul_eq m` and `Equiv.Perm.card_of_cycleType m`
  compute this cardinality.

-/

open scoped Pointwise

section CycleTypes

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace Equiv.Perm

open Equiv

open scoped Pointwise

-- USEFUL ?
/-- If `c` is a cycle of `g`, `x` belongs to the support of `g`
  and `y` belongs to the support of `c`,
  then `c` is the cycle of `x` for `g` iff `x` and `y` belong to the same cycle. -/
theorem eq_cycleOf_iff_sameCycle {g : Perm α}
    {c : g.cycleFactorsFinset} {x y : α}
    (hx : x ∈ g.support) (hy : y ∈ support c):
    c = g.cycleOf x ↔ g.SameCycle y x := by
  rw [cycle_is_cycleOf hy c.prop]
  refine ⟨?_, SameCycle.cycleOf_eq⟩
  intro hx'
  rw [mem_support, ← cycleOf_apply_self, ← mem_support, ← hx', mem_support_cycleOf_iff] at hx
  exact hx.1

/-- If `x` and `y` are in the same cycle for `g`,
  `c` is a cycle of `g`, and `y` belongs to the support of `c`,
  then `c` is the cycle of `x` for `g`. -/
theorem SameCycle.eq_cycleOf
    {g : Perm α} (c : g.cycleFactorsFinset) {x y}
    (hx : g.SameCycle y x) (hy : y ∈ support c):
    c = g.cycleOf x := by
  rw [cycle_is_cycleOf hy c.prop, SameCycle.cycleOf_eq hx]

theorem sameCycle_of_mem_support_cycleOf {g : Perm α} {x y : α} (hy : y ∈ support (g.cycleOf x)) :
    g.SameCycle y x := by
  rw [mem_support_cycleOf_iff, sameCycle_comm] at hy
  exact hy.1

theorem sameCycle_of_mem_support
    {g : Perm α} {x : α} (hx : x ∈ g.support) :
    ∃ c : g.cycleFactorsFinset, ∀ y ∈ support c, g.SameCycle y x := by
  use ⟨g.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr hx⟩
  apply sameCycle_of_mem_support_cycleOf

theorem commute_of_mem_cycleFactorsFinset_iff {g k c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    Commute k c ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ k x ∈ c.support,
        k.subtypePerm hc' ∈ Subgroup.zpowers
          (g.subtypePerm (mem_cycleFactorsFinset_support hc)) := by
  rw [IsCycle.commute_iff' (mem_cycleFactorsFinset_iff.mp hc).1]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro n
  unfold subtypePermOfSupport
  rw [Equiv.Perm.subtypePerm_on_cycleFactorsFinset hc]
  rfl

theorem zpow_mod_card_support_cycleOf_self_apply [Fintype α]
    (f : Perm α) (n : ℤ) (x : α) :
    (f ^ (n % ((cycleOf f x).support.card) : ℤ) : Perm α) x = (f ^ n) x := by
  by_cases hx : f x = x
  · rw [zpow_apply_eq_self_of_apply_eq_self hx, zpow_apply_eq_self_of_apply_eq_self hx]
  · rw [← f.cycleOf_zpow_apply_self, ← f.cycleOf_zpow_apply_self,
      ← (f.isCycle_cycleOf hx).orderOf, zpow_mod_orderOf]

end Equiv.Perm

@[to_additive instDecidablePredMemSetFixedByAddOfDecidableEq]
instance {α β : Type*} [Monoid α] [DecidableEq β] [MulAction α β] (a : α) :
    DecidablePred fun b : β => b ∈ MulAction.fixedBy β a := by
  intro b
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
  infer_instance

/-- The `toFun` map of the description of the centralizer of `g : Equiv.Perm α` -/
def Equiv.permConjStabilizerFun (g : Equiv.Perm α) :
    (Equiv.Perm (MulAction.fixedBy α g) ×
        ∀ c ∈ g.cycleFactorsFinset, Subgroup.zpowers (c : Equiv.Perm α)) →
      Equiv.Perm α :=
  fun uv : Equiv.Perm (MulAction.fixedBy α g) ×
      ∀ c ∈ g.cycleFactorsFinset, Subgroup.zpowers (c : Equiv.Perm α) =>
  Equiv.Perm.ofSubtype uv.fst *
    Finset.noncommProd g.cycleFactorsFinset
      (fun c => dite (c ∈ g.cycleFactorsFinset) (fun hc => uv.snd c hc) fun hc => 1)
      fun c hc d hd h => by
      simp only [Finset.mem_coe] at hc hd
      simp only [dif_pos hd, dif_pos hc]
      obtain ⟨m, hc'⟩ := Subgroup.mem_zpowers_iff.mp (uv.snd c hc).prop
      obtain ⟨n, hd'⟩ := Subgroup.mem_zpowers_iff.mp (uv.snd d hd).prop
      rw [← hc', ← hd']
      apply Commute.zpow_zpow
      exact g.cycleFactorsFinset_mem_commute hc hd h

theorem commute_ofSubtype_disjoint {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a, ¬(p a ∧ q a)) (x : Equiv.Perm (Subtype p)) (y : Equiv.Perm (Subtype q)) :
    Commute (Equiv.Perm.ofSubtype x) (Equiv.Perm.ofSubtype y) := by
  apply Equiv.Perm.Disjoint.commute
  intro a
  by_cases hx : p a
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem y]
    apply Or.intro_right; rfl
    exact not_and.mp (hpq a) hx
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem x hx]
    apply Or.intro_left; rfl

end CycleTypes

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α] (g : Equiv.Perm α)

namespace OnCycleFactors

/-- The action by conjugation of `ConjAct (Equiv.Perm α)`
  on the cycles of a given permutation -/
def subMulAction : SubMulAction
    (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) (Equiv.Perm α) where
  carrier := (g.cycleFactorsFinset : Set (Equiv.Perm α))
  smul_mem' k c hc := by
    have := Equiv.Perm.cycleFactorsFinset_conj_eq (↑k) g
    rw [MulAction.mem_stabilizer_iff.mp k.prop] at this
    rw [this, Finset.coe_smul_finset]
    exact ⟨c, hc, rfl⟩

/-- The conjugation action of `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  on the cycles of a given permutation -/
instance mulAction :
    MulAction (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
      (g.cycleFactorsFinset : Set (Equiv.Perm α)) :=
  (subMulAction g).mulAction

/-- The canonical morphism from `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  to the group of permutations of `g.cycleFactorsFinset` -/
def φ := MulAction.toPermHom (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (g.cycleFactorsFinset : Set (Equiv.Perm α))

theorem φ_eq (k : ConjAct (Equiv.Perm α))
    (hk : k ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) :
    (φ g ⟨k, hk⟩ ⟨c, hc⟩ : Equiv.Perm α) = k • c := rfl

theorem φ_eq' (k : Equiv.Perm α)
    (hk : k ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) :
    (φ g ⟨ConjAct.toConjAct k, hk⟩ ⟨c, hc⟩ : Equiv.Perm α) = k * c * k⁻¹ :=  rfl

theorem φ_eq'2 (k : MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (c : g.cycleFactorsFinset) :
    (φ g k c : Equiv.Perm α) = ConjAct.ofConjAct (k : ConjAct (Equiv.Perm α)) *
      (c : Equiv.Perm α) * (ConjAct.ofConjAct (k : ConjAct (Equiv.Perm α))) ⁻¹ :=  rfl

variable {g}

/-- A `Basis` of a permutation is a choice of an element in each of its cycles -/
class _root_.Equiv.Perm.Basis (g : Equiv.Perm α) where
  /-- A choice of elements in each cycle -/
  (toFun : g.cycleFactorsFinset → α)
  /-- For each cycle, the chosen element belongs to the cycle -/
  (mem_support : ∀ c, toFun c ∈ (c : Equiv.Perm α).support)

/-- A `Basis` of a permutation is a choice of an element in each of its cycles -/
def _root_.Equiv.Perm.Basis' (g : Equiv.Perm α) :=
  Π (c : g.cycleFactorsFinset), (c : Equiv.Perm α).support

instance (g : Equiv.Perm α) :
  DFunLike (Equiv.Perm.Basis g) (g.cycleFactorsFinset) (fun _ => α) where
  coe a := a.toFun
  coe_injective' a a' _ := by cases a; cases a'; congr

theorem _root_.Equiv.Perm.Basis.nonempty (g : Equiv.Perm α) :
    Nonempty (Equiv.Perm.Basis g) := by
  have (c : g.cycleFactorsFinset) : (c : Equiv.Perm α).support.Nonempty :=
    Equiv.Perm.IsCycle.nonempty_support (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1
  exact ⟨fun c ↦ (this c).choose, fun c ↦ (this c).choose_spec⟩

-- delete?
theorem _root_.Equiv.Perm.Basis.mem_support'
    (a : Equiv.Perm.Basis g) (c : g.cycleFactorsFinset) :
    a c ∈ Equiv.Perm.support g :=
  Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop (a.mem_support c)

theorem _root_.Equiv.Perm.Basis.cycleOf_eq
    (a : Equiv.Perm.Basis g) (c : g.cycleFactorsFinset) :
    g.cycleOf (a c) = c :=
  (Equiv.Perm.cycle_is_cycleOf (a.mem_support c) c.prop).symm

/-- Given a basis `a` of `g`, this is the basic function that allows
  to define the inverse of `Equiv.Perm.OnCycleFactors.φ` :
  `Kf a e ⟨c, i⟩ = (g ^ i) (a (e c))` -/
def Kf (a : Basis g) (e : Perm g.cycleFactorsFinset) (x : g.cycleFactorsFinset × ℤ) : α :=
  (g ^ x.2) (a (e x.1))

/- -- This version would have been simpler, but doesn't work later
 -- because of the use of Function.extend which requires functions
 -- with *one* argument.
def Kf (a : Equiv.Perm.Basis g) (e : Equiv.Perm g.cycleFactorsFinset)
  (c : g.cycleFactorsFinset) (i : ℤ) : α :=
  (g ^ i) (a (e c))
-/
theorem Kf_def (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i : ℤ} :
    Kf a e ⟨c, i⟩ = (g ^ i) (a (e c)) :=
  rfl

theorem Kf_def_zero (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} :
    Kf a e ⟨c, 0⟩ = a (e c) :=
  rfl

theorem Kf_def_one (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} :
    Kf a e ⟨c, 1⟩ = g (a (e c)) :=
  rfl

/-- The multiplicative-additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_mul_add  (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset}
    {e e' : Equiv.Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a (e' * e) ⟨c, i + j⟩ = (g ^ i) (Kf a e' ⟨e c, j⟩) := by
  simp only [Kf_def, zpow_add, Equiv.Perm.coe_mul, Function.comp_apply]

/-- The additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_add  (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset}
    {e : Equiv.Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a 1 ⟨e c, j⟩) := by
  rw [← Kf_mul_add, one_mul]

/-- The additive property of `Equiv.Perm.OnCycleFactors.Kf` -/
theorem Kf_add'  (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset}
    {e : Equiv.Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a e ⟨c, j⟩) := by
  rw [← mul_one e, Kf_mul_add, mul_one]
  rfl

-- was ha''
-- DELETE?
theorem _root_.Equiv.Perm.Basis.eq_cycleOf (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset} {i : ℤ} :
    c = g.cycleOf ((g ^ i) (a c)) := by
  rw [Equiv.Perm.cycleOf_self_apply_zpow]
    -- ← Equiv.Perm.cycle_is_cycleOf (a.mem_support c) c.prop]
  rw [a.cycleOf_eq]

theorem _root_.Equiv.Perm.Basis.eq_cycleOf' (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset} {e : Equiv.Perm g.cycleFactorsFinset} {i : ℤ} :
    e c = g.cycleOf (Kf a e ⟨c, i⟩) := by
  rw [Kf_def, Equiv.Perm.cycleOf_self_apply_zpow, a.cycleOf_eq]

theorem _root_.Equiv.Perm.Basis.Kf_apply (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i : ℤ} :
    g (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  rw [Kf_def, Kf_def, ← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm 1 i]

theorem _root_.Equiv.Perm.Basis.Kf_apply' (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c d : g.cycleFactorsFinset} {i : ℤ}
    (hd : d = e c) :
    (d : Equiv.Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  -- Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) appartient au cycle de e c
  rw [hd]
  rw [Equiv.Perm.Basis.eq_cycleOf', Equiv.Perm.cycleOf_apply_self,
    Equiv.Perm.Basis.Kf_apply]

theorem _root_.Equiv.Perm.Basis.Kf_apply'' (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c d : g.cycleFactorsFinset} {i : ℤ}
    (hd' : d ≠ e c) :
    (d : Equiv.Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i⟩ := by
  suffices hdc : (d : Equiv.Perm α).Disjoint (e c : Equiv.Perm α) by
    apply Or.resolve_right (Equiv.Perm.disjoint_iff_eq_or_eq.mp hdc (Kf a e ⟨c, i⟩))
    rw [Equiv.Perm.Basis.eq_cycleOf', Equiv.Perm.cycleOf_apply_self,
      ← Equiv.Perm.cycleOf_eq_one_iff, ← Equiv.Perm.Basis.eq_cycleOf']
    apply Equiv.Perm.IsCycle.ne_one
    refine' (Equiv.Perm.mem_cycleFactorsFinset_iff.mp (e c).prop).1
  apply g.cycleFactorsFinset_pairwise_disjoint d.prop (e c).prop
  rw [Function.Injective.ne_iff Subtype.coe_injective]
  exact hd'

theorem _root_.Equiv.Perm.Basis.Kf_factorsThrough (a : Equiv.Perm.Basis g)
    {e e' : Equiv.Perm g.cycleFactorsFinset}
    (hee' : ∀ c : g.cycleFactorsFinset,
        (e c : Equiv.Perm α).support.card = (e' c : Equiv.Perm α).support.card) :
    (Kf a e').FactorsThrough (Kf a e) := by
  --    Kf e ci = Kf e dj → Kf e' ci = Kf e' dj,
  rintro ⟨c, i⟩ ⟨d, j⟩ He
  simp only [Kf_def] at He ⊢
  suffices hcd : c = d by
    rw [hcd] at He ⊢
    rw [g.zpow_eq_zpow_on_iff,
      ← Equiv.Perm.cycle_is_cycleOf (a := a (e d)) (a.mem_support _) (e d).prop] at He
    rw [g.zpow_eq_zpow_on_iff,
      ← Equiv.Perm.cycle_is_cycleOf (a := a (e' d)) (a.mem_support _) (e' d).prop, ← hee' d]
    exact He
    · rw [← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
        ← Equiv.Perm.cycle_is_cycleOf (a := a (e' d)) (a.mem_support _) (e' d).prop]
      exact (e' d).prop
    · rw [← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
        ← Equiv.Perm.cycle_is_cycleOf (a := a (e d)) (a.mem_support _) (e d).prop]
      exact (e d).prop
  · -- d = c
    apply Equiv.injective e
    rw [← Subtype.coe_inj, Equiv.Perm.Basis.eq_cycleOf, Equiv.Perm.Basis.eq_cycleOf, He]

/-- Given a basis `a` of `g` and a permutation `τ` of `g.cycleFactorsFinset`,
  `k a τ` is a permutation that acts -/
noncomputable def k (a : Equiv.Perm.Basis g) (τ : Equiv.Perm g.cycleFactorsFinset) :=
  Function.extend (Kf a 1) (Kf a τ) id

theorem k_apply (a : Equiv.Perm.Basis g)
    (c : g.cycleFactorsFinset) (i : ℤ) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (Kf a 1 ⟨c, i⟩) = Kf a τ ⟨c, i⟩ := by
  simp only [k]
  rw [Function.FactorsThrough.extend_apply (Equiv.Perm.Basis.Kf_factorsThrough a _) id ⟨c, i⟩]
  · intro c
    simp only [← hτ c, Equiv.Perm.coe_one, id_eq]

theorem k_apply_base (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset} {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (a c) = a (τ c) :=
  k_apply a c 0 hτ

theorem k_apply_of_not_mem_support (a : Equiv.Perm.Basis g)
    {τ : Equiv.Perm g.cycleFactorsFinset} (x : α) (hx : x ∉ g.support) :
    k a τ x = x := by
  simp only [k]
  rw [Function.extend_apply']
  · simp only [id_eq]
  · intro hyp
    apply hx
    obtain ⟨⟨c, i⟩, rfl⟩ := hyp
    rw [Kf_def, Equiv.Perm.zpow_apply_mem_support]
    exact Basis.mem_support' a _

theorem mem_support_iff_exists_Kf (a : Equiv.Perm.Basis g) (x : α) :
    x ∈ g.support ↔
    ∃ (c : g.cycleFactorsFinset) (i : ℤ), x = Kf a 1 ⟨c, i⟩ := by
  constructor
  · intro hx
    rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff] at hx
    use ⟨g.cycleOf x, hx⟩
    simp only [Kf_def, Equiv.Perm.coe_one, id_eq]
    let ha := a.mem_support ⟨g.cycleOf x, hx⟩
    simp only [Subtype.coe_mk, Equiv.Perm.mem_support_cycleOf_iff] at ha
    obtain ⟨i, hi⟩ := ha.1.symm
    exact ⟨i, hi.symm⟩
  · rintro ⟨c, i, rfl⟩
    simp only [Kf_def, Equiv.Perm.zpow_apply_mem_support, Equiv.Perm.coe_one, id_eq]
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop
    apply a.mem_support

theorem k_commute_zpow (a : Equiv.Perm.Basis g) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) (j : ℤ) :
    k a τ ∘ (g ^ j : Equiv.Perm α) = (g ^ j : Equiv.Perm α) ∘ k a τ := by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · rw [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [← Kf_add']
    rw [k_apply a c (j + i) hτ]
    rw [k_apply a c i hτ]
    rw [Kf_add']
  · rw [k_apply_of_not_mem_support a x hx]
    rw [k_apply_of_not_mem_support a ((g ^ j : Equiv.Perm α) x) _]
    rw [Equiv.Perm.zpow_apply_mem_support]
    exact hx

theorem k_commute (a : Equiv.Perm.Basis g) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ ∘ g = g ∘ k a τ := by
  simpa only [zpow_one] using k_commute_zpow a hτ 1

theorem k_apply_gen (a : Equiv.Perm.Basis g) {c : g.cycleFactorsFinset} {i : ℤ}
    {σ τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (Kf a σ ⟨c, i⟩) = Kf a (τ * σ) ⟨c, i⟩ := by
  simp only [Kf_def]
  rw [← Function.comp_apply (f := k a τ), k_commute_zpow a hτ, Function.comp_apply]
  apply congr_arg
  dsimp
  have : ∀ (d) (τ : Equiv.Perm g.cycleFactorsFinset),
    a (τ d) = Kf a 1 (τ d, 0) :=
    fun d τ ↦ rfl
  rw [this _ σ,
    k_apply a (σ c) 0 hτ, ← Function.comp_apply (f := τ), ← Equiv.Perm.coe_mul,
    this _ (τ * σ)]
  rfl

theorem k_mul (a : Equiv.Perm.Basis g) (σ : Equiv.Perm g.cycleFactorsFinset)
    (hσ : ∀ c, (σ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card)
    (τ : Equiv.Perm g.cycleFactorsFinset)
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a σ ∘ k a τ = k a (σ * τ) := by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [k_apply a c i hτ, k_apply_gen _]
    rw [k_apply_gen]
    simp only [mul_one]
    · intro c
      rw [Equiv.Perm.coe_mul, Function.comp_apply, hσ, hτ]
    exact hσ
  · simp only [k_apply_of_not_mem_support a x hx]

theorem k_one (a : Equiv.Perm.Basis g) : k a (1 : Equiv.Perm g.cycleFactorsFinset) = id := by
  ext x
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [k_apply]
    rfl
    intro c; rfl
  simp only [id_eq, k_apply_of_not_mem_support a x hx]

theorem k_bij (a : Equiv.Perm.Basis g) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    Function.Bijective (k a τ) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine' And.intro _ rfl
  rw [Function.surjective_iff_hasRightInverse]
  use k a τ⁻¹
  rw [Function.rightInverse_iff_comp]
  rw [k_mul]; rw [mul_inv_self]; rw [k_one]
  exact hτ
  intro c; rw [← hτ (τ⁻¹ c), Equiv.Perm.apply_inv_self]

theorem k_cycle_apply (a : Equiv.Perm.Basis g) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card)
    (c : g.cycleFactorsFinset) (x : α) :
    k a τ ((c : Equiv.Perm α) x) = (τ c : Equiv.Perm α) (k a τ x) := by
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨d, j, rfl⟩ := hx
    by_cases hcd : c = d
    · rw [hcd, Equiv.Perm.Basis.Kf_apply',
        k_apply a d _ hτ, k_apply a d _ hτ, ← Equiv.Perm.Basis.Kf_apply']
      rfl
      simp only [Equiv.Perm.coe_one, id_eq]
    · rw [Equiv.Perm.Basis.Kf_apply'' a,
        k_apply a _ _ hτ, Equiv.Perm.Basis.Kf_apply'' a]
      exact (Equiv.injective τ).ne_iff.mpr hcd
      exact hcd
  · suffices ∀ (c : g.cycleFactorsFinset), (c : Equiv.Perm α) x = x by
      simp only [this, k_apply_of_not_mem_support a x hx]
    · intro c
      rw [← Equiv.Perm.not_mem_support]
      apply Finset.not_mem_mono _ hx
      exact Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop

theorem hφ_eq_card_of_mem_range {τ} (hτ : τ ∈ (φ g).range) (c) :
    (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hτ
  rw [φ_eq, ConjAct.smul_def, Equiv.Perm.support_conj]
  apply Finset.card_map

/-- Given `a : g.Basis` and a permutation of g.cycleFactorsFinset that
  preserve the lengths of the cycles, the permutation of `α` that
  moves the `Basis` and commutes with `g`
  -/
noncomputable def φ'Fun (a : Equiv.Perm.Basis g)
    {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    Equiv.Perm α :=
  Equiv.ofBijective (k a τ) (k_bij a hτ)

theorem φ'_mem_stabilizer (a : Equiv.Perm.Basis g)
    {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    ConjAct.toConjAct (φ'Fun a hτ) ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g := by
  rw [MulAction.mem_stabilizer_iff]
  rw [ConjAct.smul_def]
  rw [ConjAct.ofConjAct_toConjAct]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Equiv.Perm.coe_mul]
  simp only [φ'Fun]
  simp only [Function.comp_apply, Equiv.ofBijective_apply]
  rw [← Function.comp_apply (f := k a τ)]
  rw [k_commute a hτ]
  rfl

variable (g)

/-- The range of `Equiv.Perm.OnCycleFactors.φ` -/
def Iφ : Subgroup (Equiv.Perm g.cycleFactorsFinset) where
  carrier := {τ | ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_one, id_eq, eq_self_iff_true, imp_true_iff]
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Subtype.forall, Set.mem_setOf_eq, Equiv.Perm.coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ hτ
    intro c hc
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ
    simp only [Subtype.forall, Set.mem_setOf_eq]
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ
    intro c hc
    rw [← hσ ]
    simp only [Finset.coe_mem, Subtype.coe_eta, Equiv.Perm.apply_inv_self]
    simp only [Finset.coe_mem]

variable {g}

theorem mem_Iφ_iff {τ : Equiv.Perm g.cycleFactorsFinset} :
    τ ∈ Iφ g ↔ ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  simp only [Iφ]; rfl

/-- Given `a : Equiv.Perm.Basis g`,
  we define a right inverse of `Equiv.Perm.OnCycleFactors.φ`, on `Iφ g` -/
noncomputable
def φ' (a : Equiv.Perm.Basis g) :
    Iφ g →* MulAction.stabilizer (ConjAct (Equiv.Perm α)) g  where
  toFun τhτ :=
    ⟨ConjAct.toConjAct (φ'Fun a (mem_Iφ_iff.mp τhτ.prop)),
      φ'_mem_stabilizer a (mem_Iφ_iff.mp τhτ.prop)⟩
  map_one' := by
    simp only [OneMemClass.coe_one, Submonoid.mk_eq_one, MulEquivClass.map_eq_one_iff]
    ext x
    simp only [φ'Fun, k_one, Equiv.ofBijective_apply, id_eq, Equiv.Perm.coe_one]
  map_mul' σ τ := by
    simp only [Subgroup.coe_mul, Submonoid.mk_mul_mk, Subtype.mk_eq_mk, ← ConjAct.toConjAct_mul]
    apply congr_arg
    ext x
    simp only [φ'Fun, ← k_mul _ _ σ.prop _ τ.prop,
      Equiv.ofBijective_apply, Function.comp_apply, Equiv.Perm.coe_mul]

theorem φ'_apply' (a : Equiv.Perm.Basis g) {τ} (hτ) (x) :
    (ConjAct.ofConjAct (φ' a ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))) x = k a τ x :=
  rfl

theorem φ'_apply (a : Equiv.Perm.Basis g) (τ : Iφ g) (x) :
    ConjAct.ofConjAct (φ' a τ : ConjAct (Equiv.Perm α)) x = k a τ.val x :=
  rfl

theorem φ'_support_le (a : Equiv.Perm.Basis g) (τ : Iφ g) :
    (ConjAct.ofConjAct (φ' a τ : ConjAct (Equiv.Perm α))).support ≤
      g.support := by
  intro x
  simp only [Equiv.Perm.mem_support]
  intro hx' hx
  apply hx'
  rw [← Equiv.Perm.not_mem_support] at hx
  exact k_apply_of_not_mem_support a x hx

theorem hφ'_equivariant (a : Equiv.Perm.Basis g) (τ : Iφ g) (c : g.cycleFactorsFinset) :
    (φ' a τ  : ConjAct (Equiv.Perm α)) • (c : Equiv.Perm α) = τ.val c := by
  rw [ConjAct.smul_def]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  exact k_cycle_apply a τ.prop c x

theorem hφ'_is_rightInverse (a : Equiv.Perm.Basis g) (τ : Iφ g) :
    (φ g) ((φ' a) τ) = (τ : Equiv.Perm g.cycleFactorsFinset) := by
  apply Equiv.Perm.ext
  rintro ⟨c, hc⟩
  rw [← Subtype.coe_inj, φ_eq, hφ'_equivariant a τ ⟨c, hc⟩]
  rfl

theorem Iφ_eq_range : Iφ g = (φ g).range := by
  obtain ⟨a⟩ := Basis.nonempty g
  ext τ
  constructor
  · exact fun hτ ↦ ⟨(φ' a) ⟨τ, hτ⟩, hφ'_is_rightInverse a ⟨τ, hτ⟩⟩
  · rw [mem_Iφ_iff]
    exact hφ_eq_card_of_mem_range

theorem hφ_mem_range_iff {τ} : τ ∈ (φ g).range ↔
    ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  simp only [← Iφ_eq_range, mem_Iφ_iff]
  rfl

-- FIND A BETTER NAME
/-- The lengths of the cycles -/
abbrev fsc₀ (c : g.cycleFactorsFinset) : ℕ := (c : Equiv.Perm α).support.card

-- FIND A BETTER NAME
lemma hlc₀ (n : ℕ) :
    Fintype.card {c : g.cycleFactorsFinset // fsc₀ c = n } = g.cycleType.count n  := by
  apply symm
  -- Rewrite the Multiset.count as a Fintype.card
  have nd := (Finset.filter (fun a ↦ n = (Finset.card ∘ Equiv.Perm.support) a)
    (Equiv.Perm.cycleFactorsFinset g)).nodup
  rw [Equiv.Perm.cycleType_def, Multiset.count_map, ← Finset.filter_val]
  rw [← Multiset.toFinset_card_of_nodup nd, ← Multiset.toFinset_eq nd]
  simp only [Function.comp_apply, Finset.filter_congr_decidable, Finset.filter_val]
  rw [← Set.ncard_coe_Finset]
  -- Rewrite the RHS using an equiv as a Set.ncard
  rw [← Nat.card_eq_fintype_card, ← Set.coe_setOf, Set.Nat.card_coe_set_eq]
  -- Ugly hack
  change _ = Set.ncard { x : g.cycleFactorsFinset |
    (x : Equiv.Perm α) ∈ { x |  Finset.card (Equiv.Perm.support x) = n } }
  simp only [Set.ncard_subtype]
  congr
  ext c
  simp [and_comm, eq_comm]

theorem hφ_range'₀ :
    ((φ g).range : Set (Equiv.Perm (g.cycleFactorsFinset : Set (Equiv.Perm α)))) =
      {τ : Equiv.Perm g.cycleFactorsFinset | fsc₀ ∘ τ = fsc₀ } := by
  rw [← Iφ_eq_range]
  ext τ
  simp only [Finset.coe_sort_coe, Set.mem_setOf_eq, Function.funext_iff,
    Function.comp_apply, SetLike.mem_coe, mem_Iφ_iff, fsc₀]


/-
theorem hφ_range' :
    ((φ g).range : Set (Equiv.Perm (g.cycleFactorsFinset : Set (Equiv.Perm α)))) =
      {τ : Equiv.Perm g.cycleFactorsFinset | fsc ∘ τ = fsc} := by
  rw [← Iφ_eq_range]
  ext τ
  simp only [Finset.coe_sort_coe, Set.mem_setOf_eq, Function.funext_iff, Function.comp_apply]
  simp only [SetLike.mem_coe, mem_Iφ_iff]
  apply forall_congr'
  intro c
  simp only [← Function.Injective.eq_iff Fin.val_injective, fsc]
-/

/-
theorem hφ_range_card' :
    Nat.card (φ g).range =
      Fintype.card {k : Equiv.Perm g.cycleFactorsFinset | fsc ∘ k = fsc} := by
  simp_rw [← hφ_range', Nat.card_eq_fintype_card]
  rfl
-/

open BigOperators Nat

theorem hφ_range_card :
    Fintype.card (φ g).range =
      ∏ n in g.cycleType.toFinset, (g.cycleType.count n)! := by
  suffices Fintype.card (φ g).range =
    Fintype.card { k : Equiv.Perm g.cycleFactorsFinset | fsc₀ ∘ k = fsc₀ } by
    simp only [this, Set.coe_setOf, DomMulAct.stabilizer_card', hlc₀]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    · ext n
      simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, fsc₀, true_and,
        Subtype.exists, exists_prop, Multiset.mem_toFinset]
      simp only [cycleType_def, Function.comp_apply, Multiset.mem_map, Finset.mem_val]
  · simp_rw [← hφ_range'₀]
    rfl

/-- A permutation `z : Equiv.Perm α` belongs to the kernel of `φ g` iff
  it commutes with each cycle of `g` -/
theorem hφ_mem_ker_iff (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈ (φ g).ker.map
      (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).subtype  ↔
        ∀ t ∈ g.cycleFactorsFinset, Commute z t := by
  constructor
  · intro hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨⟨k, hkK⟩, hk, hk'⟩ := hz
    simp only [MonoidHom.mem_ker] at hk
    intro t ht
    change z * t = t * z
    rw [← mul_inv_eq_iff_eq_mul, ← MulAut.conj_apply, ← ConjAct.ofConjAct_toConjAct z,
      ← ConjAct.smul_eq_mulAut_conj _ t, ← hk']
    simp only [Subgroup.coeSubtype, Subgroup.coe_mk]
    simp only [← φ_eq g k hkK t ht, hk]
    rfl
  · intro H
    rw [Subgroup.mem_map]
    use! ConjAct.toConjAct z
    · rw [MulAction.mem_stabilizer_iff]
      rw [ConjAct.smul_eq_mulAut_conj]
      rw [MulAut.conj_apply]
      rw [mul_inv_eq_iff_eq_mul]
      rw [ConjAct.ofConjAct_toConjAct]
      exact Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute z g H
    simp only [MonoidHom.mem_ker]
    constructor
    · ext ⟨c, hc⟩
      rw [φ_eq']
      rw [H c hc]
      simp only [mul_inv_cancel_right, Equiv.Perm.coe_one, id_eq, Subtype.coe_mk]
    · simp only [Subgroup.coeSubtype, Subgroup.coe_mk]

/- delete
lemma _root_.Finset.noncommProd_eq_one
    {α : Type*} [DecidableEq α] {β : Type*} [Monoid β]
    (s : Finset α) (f : α → β)
    (comm : Set.Pairwise ↑s fun a b => Commute (f a) (f b))
    (hf : ∀ a ∈ s, f a = 1) :
    s.noncommProd f comm = 1 := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]
  | insert ha hs =>
      rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ ha]
      rw [hf _ (Finset.mem_insert_self _ _), one_mul]
      apply hs
      intro a ha
      exact hf _ (Finset.mem_insert_of_mem ha)
-/

lemma _root_.Equiv.Perm.cycleOf_ne_one_iff_mem_cycleFactorsFinset (g : Equiv.Perm α) {x : α} :
    g.cycleOf x ≠ 1 ↔ g.cycleOf x ∈ g.cycleFactorsFinset := by
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.mem_support,
        ne_eq, Equiv.Perm.cycleOf_eq_one_iff]

/-- The direct description of the centralizer of `g` -/
def θAux (g : Equiv.Perm α) (k : Equiv.Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (x : α) : α :=
  if hx : g.cycleOf x ∈ g.cycleFactorsFinset
    then (v ⟨g.cycleOf x, hx⟩ : Equiv.Perm α) x
    else Equiv.Perm.ofSubtype k x

lemma θAux_apply_of_not_mem_cycleFactorsFinset {k} {v} {x}
    (hx : g.cycleOf x ∉ g.cycleFactorsFinset) :
    θAux g k v x = Equiv.Perm.ofSubtype k x := by
  rw [θAux, dif_neg hx]

lemma θAux_apply_of_mem_fixedPoints {k} {v} {x}
    (hx : x ∈ Function.fixedPoints g) :
    θAux g k v x = Equiv.Perm.ofSubtype k x := by
  rw [θAux, dif_neg]
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support]
  exact hx

lemma θAux_apply_of_mem_fixedPoints_mem {k} {v} {x}
    (hx : x ∈ Function.fixedPoints g) :
    θAux g k v x ∈ Function.fixedPoints g := by
  rw [θAux_apply_of_mem_fixedPoints hx, Equiv.Perm.ofSubtype_apply_of_mem k hx]
  exact (k _).prop

lemma θAux_apply_of_cycleOf_eq {k} {v} {x} (c : g.cycleFactorsFinset)
    (hx : g.cycleOf x = ↑c) : θAux g k v x = (v c : Equiv.Perm α) x := by
  suffices c = ⟨g.cycleOf x, by simp only [hx, c.prop]⟩ by
    rw [this, θAux, dif_pos]
  simp only [← Subtype.coe_inj, hx]

lemma θAux_apply_of_cycleOf_eq_mem {k} {v} {x} (c : g.cycleFactorsFinset)
    (hx : g.cycleOf x = ↑c) :
    g.cycleOf (θAux g k v x) = ↑c := by
  rw [θAux_apply_of_cycleOf_eq c hx]
  obtain ⟨m, hm⟩ := (v c).prop
  dsimp only at hm
  rw [← hm, ← hx]
  simp only [Equiv.Perm.cycleOf_zpow_apply_self, Equiv.Perm.cycleOf_self_apply_zpow]

lemma θAux_cycleOf_apply_eq {k} {v} {x} :
    g.cycleOf (θAux g k v x) = g.cycleOf x := by
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl]
    obtain ⟨m, hm⟩ := (v _).prop
    dsimp only at hm
    rw [← hm]
    simp only [Equiv.Perm.cycleOf_zpow_apply_self, Equiv.Perm.cycleOf_self_apply_zpow]
  · rw [g.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support] at hx
    rw [g.cycleOf_eq_one_iff.mpr hx, g.cycleOf_eq_one_iff,
      ← Function.mem_fixedPoints_iff]
    apply θAux_apply_of_mem_fixedPoints_mem
    exact hx

lemma θAux_one (x : α) :
    θAux g 1 1 x = x := by
  unfold θAux
  split_ifs
  · simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
  · simp only [map_one, Equiv.Perm.coe_one, id_eq]

lemma θAux_mul
    (k' : Equiv.Perm (Function.fixedPoints g))
    (v' : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (k : Equiv.Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (x : α) :
    (θAux g k' v') (θAux g k v x) =
      θAux g (k' * k : Equiv.Perm (Function.fixedPoints g))
        (v' * v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) x := by
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ (θAux_apply_of_cycleOf_eq_mem ⟨_, hx⟩ rfl),
      θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl,
      θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl]
    · simp only [ne_eq, Pi.mul_apply, Submonoid.coe_mul,
        Subgroup.coe_toSubmonoid, Equiv.Perm.coe_mul, Function.comp_apply]
  · nth_rewrite 1 [θAux, dif_neg]
    simp only [θAux, dif_neg hx]
    · simp only [map_mul, Equiv.Perm.coe_mul, Function.comp_apply]
    · simp only [θAux_cycleOf_apply_eq, hx, not_false_eq_true]

lemma θAux_inv (k) (v) :
    Function.LeftInverse (θAux g k⁻¹ v⁻¹) (θAux g k v) := fun x ↦ by
  simp only [θAux_mul, mul_left_inv, θAux_one]

/-- Given a permutation `g`, a permutation of its fixed points
  and a family of elements in the powers of the cycles of `g`,
  construct their product -/
def θFun (g : Equiv.Perm α)
    (k : Equiv.Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) :
    Equiv.Perm α := {
  toFun := θAux g k v
  invFun := θAux g k⁻¹ v⁻¹
  left_inv := θAux_inv k v
  right_inv := θAux_inv k⁻¹ v⁻¹ }

/-- The description of the kernel of `Equiv.Perm.OnCycleFactors.φ g` -/
def θ (g : Equiv.Perm α) : Equiv.Perm (Function.fixedPoints g) ×
    ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) →* Equiv.Perm α := {
  toFun     := fun kv ↦ θFun g kv.fst kv.snd
  map_one'  := by
    ext x
    simp only [θFun, Prod.fst_one, Prod.snd_one, Equiv.Perm.coe_one, id_eq,
      inv_one, Equiv.coe_fn_mk, θAux_one]
  map_mul'  := fun kv' kv ↦ by
    ext x
    simp only [θFun, Equiv.coe_fn_mk, Prod.fst_mul, Prod.snd_mul,
      Equiv.Perm.coe_mul, Equiv.coe_fn_mk, Function.comp_apply, θAux_mul] }

theorem hθ_1 (uv) (x : α) (hx : x ∈ Function.fixedPoints g) :
    θ g uv x = uv.fst ⟨x, hx⟩ := by
  unfold θ; unfold θFun
  simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
  rw [θAux_apply_of_mem_fixedPoints, Equiv.Perm.ofSubtype_apply_of_mem]
  exact hx

theorem hθ_2 (uv) (x : α) (c : g.cycleFactorsFinset)  (hx :g.cycleOf x = ↑c) :
    θ g uv x = (uv.snd c : Equiv.Perm α) x := by
  unfold θ; unfold θFun
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
  exact θAux_apply_of_cycleOf_eq c hx

theorem hθ_single (c : g.cycleFactorsFinset) :
    θ g ⟨1, (Pi.mulSingle c ⟨c, Subgroup.mem_zpowers (c : Equiv.Perm α)⟩)⟩ = c  := by
  ext x
  by_cases hx : x ∈ Function.fixedPoints g
  · simp only [hθ_1 _ x hx, Equiv.Perm.coe_one, id_eq]
    apply symm
    rw [← Equiv.Perm.not_mem_support]
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, ← Equiv.Perm.not_mem_support] at hx
    intro hx'
    apply hx
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hx'
  suffices hx' : g.cycleOf x ∈ g.cycleFactorsFinset by
    rw [hθ_2 _ x ⟨g.cycleOf x, hx'⟩ rfl]
    dsimp only
    by_cases hc : c = ⟨Equiv.Perm.cycleOf g x, hx'⟩
    · rw [hc, Pi.mulSingle_eq_same, Equiv.Perm.cycleOf_apply_self]
    · rw [Pi.mulSingle_eq_of_ne' hc]
      simp only [OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      apply symm
      rw [← Equiv.Perm.not_mem_support]
      intro hxc
      apply hc
      simp only [← Subtype.coe_inj]
      apply Equiv.Perm.cycle_is_cycleOf hxc c.prop
  rw [← Equiv.Perm.cycleOf_ne_one_iff_mem_cycleFactorsFinset]
  simp only [ne_eq, Equiv.Perm.cycleOf_eq_one_iff]
  rw [Function.mem_fixedPoints_iff] at hx
  exact hx

theorem hθ_injective (g : Equiv.Perm α) : Function.Injective (θ g) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨u, v⟩
  unfold θ; unfold θFun
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq]
  intro huv
  simp only [Subgroup.mem_bot, Prod.mk_eq_one, MonoidHom.mem_ker]
  constructor
  · ext ⟨x, hx⟩
    simp only [Equiv.Perm.coe_one, id_eq]
    conv_rhs => rw [← huv x]
    rw [θAux_apply_of_mem_fixedPoints, Equiv.Perm.ofSubtype_apply_of_mem]
    exact hx
  · ext c x
    by_cases hx : g.cycleOf x = 1
    · simp only [Equiv.Perm.cycleOf_eq_one_iff, ← Equiv.Perm.not_mem_support] at hx
      simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      obtain ⟨m, hm⟩ := (v c).prop
      rw [← hm]
      dsimp only
      rw [← Equiv.Perm.not_mem_support]
      intro hx'
      apply hx
      apply Equiv.Perm.support_zpow_le _ _ at hx'
      apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hx'
    · rw [← ne_eq, Equiv.Perm.cycleOf_ne_one_iff_mem_cycleFactorsFinset] at hx
      simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      by_cases hc : g.cycleOf x = ↑c
      · rw [← θAux_apply_of_cycleOf_eq c hc, huv]
      · obtain ⟨m, hm⟩ := (v c).prop
        rw [← hm]
        dsimp
        rw [← Equiv.Perm.not_mem_support]
        intro hx'
        refine hc (Equiv.Perm.cycle_is_cycleOf ?_ c.prop).symm
        exact Equiv.Perm.support_zpow_le _ _ hx'

theorem hφ_ker_eq_θ_range (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈
        Subgroup.map (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).subtype (φ g).ker ↔
      z ∈ (θ g).range := by
  constructor
  · rw [hφ_mem_ker_iff, Equiv.Perm.IsCycle.forall_commute_iff, MonoidHom.mem_range]
    intro Hz
    have hu : ∀ x : α,
      x ∈ Function.fixedPoints g ↔
        z x ∈ Function.fixedPoints g :=  by
      intro x
      simp only [Function.fixedPoints, Equiv.Perm.smul_def, Function.IsFixedPt]
      simp only [← Equiv.Perm.not_mem_support]
      simp only [Set.mem_setOf_eq, not_iff_not]
      constructor
      · intro hx
        let hx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf x)
          (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx)
        rw [← Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hx⟩
      · intro hzx
        let hzx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hzx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hzx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf (z x)) hzx'
        rw [Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hzx⟩
    set u := Equiv.Perm.subtypePerm z hu
    set v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers (c : Equiv.Perm α)) :=
      fun c => ⟨Equiv.Perm.ofSubtype
          (z.subtypePerm (Classical.choose (Hz c.val c.prop))),
            Classical.choose_spec (Hz c.val c.prop)⟩
    use ⟨u, v⟩
    ext x
    by_cases hx : g.cycleOf x = 1
    · rw [hθ_1 _ x]
      simp only [u, Equiv.Perm.subtypePerm_apply]
      simpa only [Equiv.Perm.cycleOf_eq_one_iff] using hx
    · rw [hθ_2 _ x ⟨g.cycleOf x, (Equiv.Perm.cycleOf_ne_one_iff_mem_cycleFactorsFinset g).mp hx⟩ rfl]
      rw [Equiv.Perm.ofSubtype_apply_of_mem]
      · rfl
      · simp only [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ne_eq]
        simpa only [Equiv.Perm.cycleOf_eq_one_iff] using hx

  · rintro ⟨⟨u, v⟩, h⟩
    rw [hφ_mem_ker_iff]

    rw [Equiv.Perm.IsCycle.forall_commute_iff]
    intro c hc
    refine ⟨?_, ?_⟩
    · intro x
      simp only [← eq_cycleOf_of_mem_cycleFactorsFinset_iff g c hc]
      rw [← h]
      unfold θ; unfold θFun
      dsimp only [MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
      rw [θAux_cycleOf_apply_eq]
    · suffices Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm z _) = v ⟨c, hc⟩ by
        rw [this]
        exact (v _).prop
      ext x
      by_cases hx : x ∈ c.support
      · rw [Equiv.Perm.ofSubtype_apply_of_mem, Equiv.Perm.subtypePerm_apply]
        dsimp
        · rw [← h, hθ_2 _ x ⟨c, hc⟩]
          exact (Equiv.Perm.cycle_is_cycleOf hx hc).symm
        exact hx
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
        · obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
          rw [← hm, eq_comm, ← Equiv.Perm.not_mem_support]
          intro hx'
          apply hx
          exact (Equiv.Perm.support_zpow_le c m) hx'
        · exact hx

lemma θ_range_eq : MonoidHom.range (θ g) =
    Subgroup.map (ConjAct.toConjAct.symm.toMonoidHom.comp
      (Subgroup.subtype (MulAction.stabilizer (ConjAct (Perm α)) g))) (MonoidHom.ker (φ g)) := by
  ext z
  rw [← hφ_ker_eq_θ_range]
  rfl

theorem hψ_range_card' (g : Equiv.Perm α) :
    Fintype.card (MonoidHom.range (θ g)) = Fintype.card (φ g).ker := by
  change Fintype.card (MonoidHom.range (θ g) : Set (Perm α)) = _
  rw [← Nat.card_eq_fintype_card, Set.Nat.card_coe_set_eq, θ_range_eq, ← Subgroup.map_map]
  rw [Subgroup.coe_map, Set.ncard_image_of_injective _ (by exact MulEquiv.injective _)]
  rw [Subgroup.coe_map, Set.ncard_image_of_injective _ (Subgroup.subtype_injective _)]
  rw [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rfl

theorem _root_.Equiv.Perm.card_fixedBy (g : Equiv.Perm α) :
    Fintype.card (MulAction.fixedBy α g) =
      Fintype.card α - g.cycleType.sum := by
  rw [Equiv.Perm.sum_cycleType, ← Finset.card_compl]
  simp only [Fintype.card_ofFinset, Set.mem_compl_iff, Finset.mem_coe,
    Equiv.Perm.mem_support, Classical.not_not]
  apply congr_arg
  ext x
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def, Finset.mem_filter, Finset.mem_univ,
    true_and_iff, Finset.mem_compl, Equiv.Perm.mem_support, Classical.not_not]

theorem hψ_range_card (g : Equiv.Perm α) :
    Fintype.card (θ g).range =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod := by
  change Fintype.card ((θ g).range : Set (Equiv.Perm α)) = _
  simp only [MonoidHom.coe_range]
  rw [Set.card_range_of_injective (hθ_injective g)]
  rw [Fintype.card_prod]
  rw [Fintype.card_perm]
  rw [Fintype.card_pi]
  apply congr_arg₂ (· * ·)
  · -- fixed points
    apply congr_arg
    exact Equiv.Perm.card_fixedBy g
  · rw [Equiv.Perm.cycleType]
    simp only [Finset.univ_eq_attach, Finset.attach_val, Function.comp_apply]
    rw [Finset.prod_attach (s := g.cycleFactorsFinset)
      (f := fun a ↦ Fintype.card (Subgroup.zpowers (a : Equiv.Perm α)))]
    rw [Finset.prod]
    apply congr_arg
    apply Multiset.map_congr rfl
    intro x hx
    rw [Fintype.card_zpowers, Equiv.Perm.IsCycle.orderOf]
    simp only [Finset.mem_val, Equiv.Perm.mem_cycleFactorsFinset_iff] at hx
    exact hx.left

lemma θ_apply_fst (k : Equiv.Perm (MulAction.fixedBy α g)) :
    θ g ⟨k, 1⟩ = Equiv.Perm.ofSubtype k := by
  ext x
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [hθ_2 _ x ⟨g.cycleOf x, hx⟩ rfl]
    simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def,
      ← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
    exact hx
  · rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support] at hx
    rw [hθ_1 _ x hx, Equiv.Perm.ofSubtype_apply_of_mem]
    rfl

lemma θ_apply_single (c : g.cycleFactorsFinset) (vc : Subgroup.zpowers (c : Equiv.Perm α)) :
    θ g ⟨1, Pi.mulSingle c vc⟩ = (vc : Equiv.Perm α) := by
  ext x
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [hθ_2 _ x ⟨g.cycleOf x, hx⟩ rfl]
    by_cases hc : g.cycleOf x = c
    · suffices c = ⟨g.cycleOf x, hx⟩ by
        rw [← this]
        simp only [Pi.mulSingle_eq_same]
      rw [← Subtype.coe_inj, ← hc]
    · obtain ⟨m, hm⟩ := vc.prop
      simp only
      rw [Pi.mulSingle_eq_of_ne]
      · simp only [OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
        rw [← eq_comm, ← hm, ← Equiv.Perm.not_mem_support]
        intro hx'
        apply hc
        apply symm
        exact Equiv.Perm.cycle_is_cycleOf (Equiv.Perm.support_zpow_le _ _ hx') c.prop
      rintro ⟨rfl⟩
      exact hc rfl
  · rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support] at hx
    rw [hθ_1 _ x hx]
    dsimp only [Equiv.Perm.coe_one, id_eq]
    obtain ⟨m, hm⟩ := vc.prop
    dsimp only at hm
    rw [← hm]
    apply symm
    rw [← Equiv.Perm.not_mem_support] at hx ⊢
    intro hx'
    apply hx
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop
    apply Equiv.Perm.support_zpow_le _ _ hx'


end OnCycleFactors

section Centralizer

open BigOperators Nat OnCycleFactors

-- Should one parenthesize the product ?
/-- Cardinality of a centralizer in `equiv.perm α` of a given `cycle_type` -/
theorem conj_stabilizer_card :
    Fintype.card (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (φ g).ker]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr (QuotientGroup.quotientKerEquivRange (φ g)).toEquiv]
  rw [hφ_range_card]
  rw [mul_comm]
  apply congr_arg₂ _ _ rfl
  · rw [← hψ_range_card, hψ_range_card', Nat.card_eq_fintype_card]

theorem _root_.Group.conj_class_eq_conj_orbit {G : Type*} [Group G] (g : G) :
    {k : G | IsConj g k} = MulAction.orbit (ConjAct G) g := by
  ext k
  simp only [Set.mem_setOf_eq, isConj_iff, MulAction.mem_orbit_iff, ConjAct.smul_def]
  constructor
  rintro ⟨c, hc⟩
  use ConjAct.toConjAct c; simp only [hc, ConjAct.ofConjAct_toConjAct]
  rintro ⟨x, hx⟩
  use ConjAct.ofConjAct x

theorem _root_.Equiv.Perm.conj_class_card_mul_eq (g : Equiv.Perm α) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} *
      (Fintype.card α - g.cycleType.sum)! *
      g.cycleType.prod *
      (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!) =
    (Fintype.card α)! := by
  classical
  simp_rw [Group.conj_class_eq_conj_orbit g]
  simp only [mul_assoc]
  rw [mul_comm]
  simp only [← mul_assoc]
  rw [← Equiv.Perm.conj_stabilizer_card g]
  rw [mul_comm]
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Equiv.Perm α)) g]
  rw [ConjAct.card, Fintype.card_perm]

theorem _root_.Multiset.prod_pos {R : Type*} [StrictOrderedCommSemiring R] (m : Multiset R)
    (h : ∀ a ∈ m, (0 : R) < a) : 0 < m.prod := by
  induction' m using Multiset.induction with a m ih
  · simp
  · rw [Multiset.prod_cons]
    exact
      mul_pos (h _ <| Multiset.mem_cons_self _ _)
        (ih fun a ha => h a <| Multiset.mem_cons_of_mem ha)

/-- Cardinality of a conjugacy class in `Equiv.Perm α` of a given `cycleType` -/
theorem conj_class_card (g : Equiv.Perm α) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} =
      (Fintype.card α)! /
        ((Fintype.card α - g.cycleType.sum)! *
          g.cycleType.prod *
          (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!)) := by
  rw [← Equiv.Perm.conj_class_card_mul_eq g]
  rw [Nat.div_eq_of_eq_mul_left _]
  simp only [← mul_assoc]
  -- This is the cardinal of the centralizer
  rw [← Equiv.Perm.conj_stabilizer_card g]
  refine' Fintype.card_pos

variable (α)

theorem card_of_cycleType_eq_zero_iff {m : Multiset ℕ} :
    (Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m).card = 0
    ↔ ¬ ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a)) := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    ← Equiv.Perm.exists_with_cycleType_iff, not_exists]
  aesop

theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m).card *
        ((Fintype.card α - m.sum)! * m.prod *
          (∏ n in m.toFinset, (m.count n)!)) =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) then (Fintype.card α)! else 0 := by
  split_ifs with hm
  · -- nonempty case
    obtain ⟨g, hg⟩ := (Equiv.Perm.exists_with_cycleType_iff α).mpr hm
    suffices (Finset.univ.filter fun h : Equiv.Perm α => h.cycleType = m) =
        Finset.univ.filter fun h : Equiv.Perm α => IsConj g h by
      rw [this]
      rw [← Fintype.card_coe]
      rw [← Equiv.Perm.conj_class_card_mul_eq g]
      simp only [Fintype.card_coe, ← Set.toFinset_card, mul_assoc]
      rw [hg]
      congr
      · simp only [Finset.univ_filter_exists, Set.toFinset_setOf]
    simp_rw [Equiv.Perm.isConj_iff_cycleType_eq, hg]
    apply Finset.filter_congr
    simp [eq_comm]
  · -- empty case
    convert MulZeroClass.zero_mul _
    exact (Equiv.Perm.card_of_cycleType_eq_zero_iff α).mpr hm

/-- Cardinality of the set of `equiv.perm α` of given `cycle_type` -/
theorem card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filter
      fun g : Equiv.Perm α => g.cycleType = m).card =
      if m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! * m.prod *
            (∏ n in m.toFinset, (m.count n)!))
      else 0 := by
  split_ifs with hm
  · -- nonempty case
    apply symm
    apply Nat.div_eq_of_eq_mul_left
    · apply Nat.mul_pos
      apply Nat.mul_pos
      · apply Nat.factorial_pos
      · apply Multiset.prod_pos
        exact fun a ha ↦ lt_of_lt_of_le (zero_lt_two) (hm.2 a ha)
      · exact Finset.prod_pos (fun _ _ ↦ Nat.factorial_pos _)
    rw [Equiv.Perm.card_of_cycleType_mul_eq, if_pos hm]
  · -- empty case
    exact (Equiv.Perm.card_of_cycleType_eq_zero_iff α).mpr hm

end Centralizer

end Equiv.Perm
