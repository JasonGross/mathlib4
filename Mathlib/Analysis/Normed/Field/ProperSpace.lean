/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Proper nontrivally normed fields

This file contains a direct result of normed fields that are `ProperSpace`s.

## Main results

* `ProperSpace.of_weaklyLocallyCompactSpace_of_nontriviallyNormedField`
-/

open Metric Filter

/-- A weakly locally compact normed field is proper. -/
lemma ProperSpace.of_weaklyLocallyCompactSpace_of_nontriviallyNormedField
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [WeaklyLocallyCompactSpace 𝕜] :
    ProperSpace 𝕜 := by
  rcases exists_isCompact_closedBall (0 : 𝕜) with ⟨r, rpos, hr⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have hC : ∀ n, IsCompact (closedBall (0 : 𝕜) (‖c‖^n * r)) := fun n ↦ by
    have : c ^ n ≠ 0 := pow_ne_zero _ <| fun h ↦ by simp [h, zero_le_one.not_lt] at hc
    convert hr.smul (c ^ n)
    ext
    simp [Set.mem_smul_set_iff_inv_smul_mem₀ this,
      inv_mul_le_iff (by simpa using norm_pos_iff.mpr this)]
  have hTop : Tendsto (fun n ↦ ‖c‖^n * r) atTop atTop :=
    Tendsto.atTop_mul_const rpos (tendsto_pow_atTop_atTop_of_one_lt hc)
  exact .of_seq_closedBall hTop (Eventually.of_forall hC)
