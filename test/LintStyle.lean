import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Common

/-! Tests for all the style linters. -/

/-! Tests for the `setOption` linter -/
section setOption

-- The warning generated by `linter.style.setOption` is not suppressed by `#guard_msgs`,
-- because the linter is run on `#guard_msgs` itself. This is a known issue, see e.g.
-- https://leanprover.zulipchat.com/#narrow/stream/348111-batteries/topic/unreachableTactic.20linter.20not.20suppressed.20by.20.60.23guard_msgs.60
-- We jump through an extra hoop here to silence the warning.
set_option linter.style.setOption false

-- All types of options are supported: boolean, numeric and string-valued.
-- On the top level, i.e. as commands.

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.all'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
set_option pp.all true

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option profiler'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
set_option profiler false

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.all'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
set_option pp.all false

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option profiler.threshold'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
set_option profiler.threshold 50

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option trace.profiler.output'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
set_option trace.profiler.output "foo"

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option debug.moduleNameAtTimeout'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
set_option debug.moduleNameAtTimeout false

-- The lint does not fire on arbitrary options.
set_option autoImplicit false

-- We also cover set_option tactics.

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.all'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
lemma tactic : True := by
  set_option pp.all true in
  trivial

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.raw.maxDepth'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
lemma tactic2 : True := by
  set_option pp.raw.maxDepth 32 in
  trivial

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.all'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
lemma tactic3 : True := by
  set_option pp.all false in
  trivial

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option trace.profiler.output'.
note: this linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option linter.style.setOption true in
lemma tactic4 : True := by
  set_option trace.profiler.output "foo" in
  trivial

-- This option is not affected, hence does not throw an error.
set_option autoImplicit true in
lemma foo' : True := trivial

-- TODO: add terms for the term form

/--
warning: The declID double__underscore contains '__', which does not follow naming conventions.
Consider using single underscores instead.
note: this linter can be disabled with `set_option linter.style.check_declID false`
-/
#guard_msgs in
set_option linter.style.check_declID true in
theorem double__underscore : True := trivial

end setOption
