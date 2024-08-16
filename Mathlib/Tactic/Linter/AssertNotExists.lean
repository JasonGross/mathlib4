/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Linter.Util
import Mathlib.Util.AssertExists

/-!
#  The "assertNotExists" linter

The "assertNotExists" style linter checks that a file starts with
```
import*
doc-module*
assert_not_imported*
assert_not_exists*
[no more assert_not_exists or assert_not_imported]
```
It emits a warning on each `assert_not_imported` command that is not preceded by
* possibly some import statements,
* possibly some doc-module strings, and
* possible some `assert_not_imported` commands,
as well as on each `assert_not_exists` command that is not preceded by
* possibly some import statements,
* possibly some doc-module strings, and
* possible some `assert_not_imported` commands, and
* possibly some `assert_not_exists` commands

in this order.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- `onlyImportsModDocsAssertImporteds stx` checks whether `stx` is the syntax for a module that
only consists of
* any number of `import` statements (possibly none) followed by
* any number of doc-module strings (possibly none) followed by
* any number of `assert_not_imported` commands (possibly none),

and nothing else.
-/
def onlyImportsModDocsAssertImporteds : Syntax → Bool
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    let dropDocs := args.toList.dropWhile (·.isOfKind ``Lean.Parser.Command.moduleDoc)
    let dropAssertNotImporteds := dropDocs.dropWhile (·.isOfKind ``commandAssert_not_imported_)
    dropAssertNotImporteds.isEmpty
  | _=> false

/-- `onlyImportsModDocsAsserts stx` checks whether `stx` is the syntax for a module that
only consists of
* any number of `import` statements (possibly none) followed by
* any number of doc-module strings (possibly none) followed by
* any number of `assert_not_imported` commands (possibly none),
* any number of `assert_not_exists` commands (possibly none),

and nothing else.
-/
def onlyImportsModDocsAsserts : Syntax → Bool
  | .node _ ``Lean.Parser.Module.module #[_header, .node _ `null args] =>
    let dropDocs := args.toList.dropWhile (·.isOfKind ``Lean.Parser.Command.moduleDoc)
    let dropAssertNotImporteds := dropDocs.dropWhile (·.isOfKind ``commandAssert_not_imported_)
    let dropAssertNotExists := dropAssertNotImporteds.dropWhile (·.isOfKind ``commandAssert_not_exists_)
    dropAssertNotExists.isEmpty
  | _=> false

/-- `parseUpToHere stx post` takes as input a `Syntax` `stx` and a `String` `post`.
It parses the file containing `stx` up to and excluding `stx`, appending `post` at the end.

The option of appending a final string to the text gives more control to avoid syntax errors,
for instance in the presence of `#guard_msgs in` or `set_option ... in`.
-/
def parseUpToHere (stx : Syntax) (post : String := "") : CommandElabM Syntax := do
  let fm ← getFileMap
  let startPos := stx.getPos?.getD default
  let upToHere : Substring:= { str := fm.source, startPos := ⟨0⟩, stopPos := startPos}
  -- append a further string after the `upToHere` content
  Parser.testParseModule (← getEnv) "linter.assertNotExists" (upToHere.toString ++ post)

/--
The "assertNotExists" style linter checks that a file starts with
```
import*
/-! module docstring -/*
assert_not_imported*
assert_not_exists*
[no more `assert_not_exists` nor `assert_not_imported`]
```
It emits a warning on each `assert_not_imported` command that is not preceded by
* possibly some import statements,
* possibly some doc-module strings, and
* possible some `assert_not_imported` commands,
as well as on each `assert_not_exists` command that is not preceded by
* possibly some import statements,
* possibly some doc-module strings, and
* possible some `assert_not_imported` commands, and
* possibly some `assert_not_exists` commands

in this order.
-/
register_option linter.style.assertNotExists : Bool := {
  defValue := true
  descr := "enable the assertNotExists linter"
}

namespace Style.AssertNotExists

/-- Gets the value of the `linter.assertNotExists` option. -/
def getLinterAssertNotExists (o : Options) : Bool :=
  Linter.getLinterValue linter.style.assertNotExists o

@[inherit_doc Mathlib.Linter.linter.style.assertNotExists]
def assertNotExistsLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterAssertNotExists (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  if stx.isOfKind ``commandAssert_not_imported_ then
    let upToStx ← parseUpToHere stx "\nassert_not_imported XXX" <|> return Syntax.missing
    if ! onlyImportsModDocsAssertImporteds upToStx then
      Linter.logLint linter.style.assertNotExists stx
        m!"`{stx}` appears too late: it can only be preceded\nby `import` statements, \
        module doc-strings and other `assert_not_exists` statements."
  else if stx.isOfKind ``commandAssert_not_exists_ then
    let upToStx ← parseUpToHere stx "\nassert_not_exists XXX" <|> return Syntax.missing
    if ! onlyImportsModDocsAsserts upToStx then
      Linter.logLint linter.style.assertNotExists stx
        m!"`{stx}` appears too late: it can only be preceded\nby `import` statements, \
        module doc-strings and other\n`assert_not_exists` statements."

initialize addLinter assertNotExistsLinter

end Style.AssertNotExists

end Mathlib.Linter
