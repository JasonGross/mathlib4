/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Positivity.Core

/-! # Finiteness tactic

This file implements a basic `finiteness` tactic, designed to solve goals of the form `*** < ∞` and
(equivalently) `*** ≠ ∞` in the extended nonnegative reals (`ENNReal`, aka `ℝ≥0∞`).

It works recursively according to the syntax of the expression. It is implemented as an `aesop` rule
set.

[TODO]: improve `finiteness` to also deal with other situations, such as balls in proper spaces with
a locally finite measure.
-/

open Aesop.BuiltinRules in
attribute [aesop (rule_sets := [finiteness]) safe -50] assumption intros

set_option linter.unusedTactic false in
add_aesop_rules safe tactic (rule_sets := [finiteness]) (by positivity)

/-- Tactic to solve goals of the form `*** < ∞` and (equivalently) `*** ≠ ∞` in the extended
nonnegative reals (`ℝ≥0∞`). -/
macro (name := finiteness) "finiteness" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { introsTransparency? := some .reducible, terminal := true, enableSimp := false })
    (rule_sets := [$(Lean.mkIdent `Finiteness):ident, -default, -builtin]))
