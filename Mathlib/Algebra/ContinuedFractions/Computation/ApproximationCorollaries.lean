/-
Copyright (c) 2021 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
import Mathlib.Algebra.ContinuedFractions.ConvergentsEquiv
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Order.LeftRightNhds

#align_import algebra.continued_fractions.computation.approximation_corollaries from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Corollaries From Approximation Lemmas (`Algebra.ContinuedFractions.Computation.Approximations`)

## Summary

We show that the gcf given by `GenContFract.of` in fact is a regular continued
fraction. Using the equivalence of the convergents computations
(`GenContFract.convs` and `GenContFract.convs'`) for
continued fractions (see `Algebra.ContinuedFractions.ConvergentsEquiv`), it follows that the
convergents computations for `GenContFract.of` are equivalent.

Moreover, we show the convergence of the continued fractions computations, that is
`(GenContFract.of v).convs` indeed computes `v` in the limit.

## Main Definitions

- `ContFract.of` returns the (regular) continued fraction of a value.

## Main Theorems

- `GenContFract.of_convs_eq_convs'` shows that the convergents computations for
  `GenContFract.of` are equivalent.
- `GenContFract.of_convergence` shows that `(GenContFract.of v).convs` converges to `v`.

## Tags

convergence, fractions
-/


variable {K : Type*} (v : K) [LinearOrderedField K] [FloorRing K]

open GenContFract (of)
open GenContFract
open scoped Topology

theorem GenContFract.of_isSimpContFract :
    (of v).IsSimpContFract := fun _ _ nth_partNum_eq =>
  of_partNum_eq_one nth_partNum_eq
#align generalized_continued_fraction.of_is_simple_continued_fraction GenContFract.of_isSimpContFract

/-- Creates the simple continued fraction of a value. -/
nonrec def SimpContFract.of : SimpContFract K :=
  ⟨of v, GenContFract.of_isSimpContFract v⟩
#align simple_continued_fraction.of SimpContFract.of

theorem SimpContFract.of_isContFract :
    (SimpContFract.of v).IsContFract := fun _ _ nth_partDen_eq =>
  lt_of_lt_of_le zero_lt_one (of_one_le_get?_partDen nth_partDen_eq)
#align simple_continued_fraction.of_is_continued_fraction SimpContFract.of_isContFract

/-- Creates the continued fraction of a value. -/
def ContFract.of : ContFract K :=
  ⟨SimpContFract.of v, SimpContFract.of_isContFract v⟩
#align continued_fraction.of ContFract.of

namespace GenContFract

theorem of_convs_eq_convs' : (of v).convs = (of v).convs' :=
  @ContFract.convs_eq_convs' _ _ (ContFract.of v)
#align generalized_continued_fraction.of_convergents_eq_convergents' GenContFract.of_convs_eq_convs'

/-- The recurrence relation for the `convs` of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fractional part.
-/
theorem convs_succ (n : ℕ) :
    (of v).convs (n + 1) = ⌊v⌋ + 1 / (of (Int.fract v)⁻¹).convs n := by
  rw [of_convs_eq_convs', convs'_succ, of_convs_eq_convs']
#align generalized_continued_fraction.convergents_succ GenContFract.convs_succ

section Convergence

/-!
### Convergence

We next show that `(GenContFract.of v).convs v` converges to `v`.
-/


variable [Archimedean K]

open Nat

theorem of_convergence_epsilon :
    ∀ ε > (0 : K), ∃ N : ℕ, ∀ n ≥ N, |v - (of v).convs n| < ε := by
  intro ε ε_pos
  -- use the archimedean property to obtain a suitable N
  rcases (exists_nat_gt (1 / ε) : ∃ N' : ℕ, 1 / ε < N') with ⟨N', one_div_ε_lt_N'⟩
  let N := max N' 5
  -- set minimum to 5 to have N ≤ fib N work
  exists N
  intro n n_ge_N
  let g := of v
  cases' Decidable.em (g.TerminatedAt n) with terminatedAt_n not_terminatedAt_n
  · have : v = g.convs n := of_correctness_of_terminatedAt terminatedAt_n
    have : v - g.convs n = 0 := sub_eq_zero.mpr this
    rw [this]
    exact mod_cast ε_pos
  · let B := g.dens n
    let nB := g.dens (n + 1)
    have abs_v_sub_conv_le : |v - g.convs n| ≤ 1 / (B * nB) :=
      abs_sub_convs_le not_terminatedAt_n
    suffices 1 / (B * nB) < ε from lt_of_le_of_lt abs_v_sub_conv_le this
    -- show that `0 < (B * nB)` and then multiply by `B * nB` to get rid of the division
    have nB_ineq : (fib (n + 2) : K) ≤ nB :=
      haveI : ¬g.TerminatedAt (n + 1 - 1) := not_terminatedAt_n
      succ_nth_fib_le_of_nth_den (Or.inr this)
    have B_ineq : (fib (n + 1) : K) ≤ B :=
      haveI : ¬g.TerminatedAt (n - 1) := mt (terminated_stable n.pred_le) not_terminatedAt_n
      succ_nth_fib_le_of_nth_den (Or.inr this)
    have zero_lt_B : 0 < B := B_ineq.trans_lt' <| mod_cast fib_pos.2 n.succ_pos
    have nB_pos : 0 < nB := nB_ineq.trans_lt' <| mod_cast fib_pos.2 <| succ_pos _
    have zero_lt_mul_conts : 0 < B * nB := by positivity
    suffices 1 < ε * (B * nB) from (div_lt_iff zero_lt_mul_conts).mpr this
    -- use that `N' ≥ n` was obtained from the archimedean property to show the following
    calc 1 < ε * (N' : K) := (div_lt_iff' ε_pos).mp one_div_ε_lt_N'
      _ ≤ ε * (B * nB) := ?_
    -- cancel `ε`
    gcongr
    calc
      (N' : K) ≤ (N : K) := by exact_mod_cast le_max_left _ _
      _ ≤ n := by exact_mod_cast n_ge_N
      _ ≤ fib n := by exact_mod_cast le_fib_self <| le_trans (le_max_right N' 5) n_ge_N
      _ ≤ fib (n + 1) := by exact_mod_cast fib_le_fib_succ
      _ ≤ fib (n + 1) * fib (n + 1) := by exact_mod_cast (fib (n + 1)).le_mul_self
      _ ≤ fib (n + 1) * fib (n + 2) := by gcongr; exact_mod_cast fib_le_fib_succ
      _ ≤ B * nB := by gcongr
#align generalized_continued_fraction.of_convergence_epsilon GenContFract.of_convergence_epsilon

theorem of_convergence [TopologicalSpace K] [OrderTopology K] :
    Filter.Tendsto (of v).convs Filter.atTop <| 𝓝 v := by
  simpa [LinearOrderedAddCommGroup.tendsto_nhds, abs_sub_comm] using of_convergence_epsilon v
#align generalized_continued_fraction.of_convergence GenContFract.of_convergence

end Convergence

end GenContFract
