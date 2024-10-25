/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Tactic.Linter.TextBased
import Cli.Basic

/-!
# Text-based style linters

This files defines the `lint-style` executable which runs all text-based style linters.
The linters themselves are defined in `Mathlib.Tactic.Linter.TextBased`.
-/

open Cli Mathlib.Linter.TextBased

open System.FilePath

/-- Verifies that every file in the `scripts` directory is documented in `scripts/README.md`. -/
def checkScriptsDocumented : IO Bool := do
  -- Retrieve all scripts (except for the `bench` directory).
  let allScripts ← (walkDir "scripts" fun p ↦ pure (p.components.getD 1 "" != "bench"))
  let allScripts := (allScripts.erase "bench").erase "README.md"
  -- TODO: drop some false positives
  --   nolint.json and noshake.json are data files; as are style-exceptions.txt and nolints-style.txt
  --   these *could* be explicitly allows, or documented as well (perhaps the latter?)
  -- Check if the README text contains each file enclosed in backticks.
  let readme : String ← IO.FS.readFile (System.mkFilePath ["scripts", "README.md"])
  IO.println s!"found {allScripts.size} scripts: {",".intercalate (allScripts.map (·.toString)).toList}"
  -- These are data files for linter exceptions: don't complain about these *for now*.
  let dataFiles := #["nolints.json", "noshake.json", "style-exceptions.txt", "nolints-style.txt"]
  let undocumented := allScripts.filter fun script ↦
    !readme.containsSubstr s!"`{script}`" && !dataFiles.contains script.toString
  if undocumented.size > 0 then
    IO.println s!"error: found {undocumented.size} undocumented scripts:\
      please describe the scripts\n\
      {String.intercalate "," (undocumented.map (·.fileName.get!)).toList}\n\
     in 'scripts/README.md'"
  return undocumented.size > 0

/-- Implementation of the `lint-style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let style : ErrorFormat := match args.hasFlag "github" with
    | true => ErrorFormat.github
    | false => ErrorFormat.humanReadable
  let fix := args.hasFlag "fix"
  -- Read all module names to lint.
  let mut allModules := #[]
  for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
    allModules := allModules.append ((← IO.FS.lines s).map (·.stripPrefix "import "))
  -- note: since we manually add "Batteries" to "Mathlib.lean", we remove it here manually
  allModules := allModules.erase "Batteries"
  let numberError ← lintModules allModules style fix
  -- If run with the `--fix` argument, return a zero exit code.
  -- Otherwise, make sure to return an exit code of at most 125,
  -- so this return value can be used further in shell scripts.
  if args.hasFlag "fix" then
    return 0
  else return min numberError 125

/-- Setting up command line options and help text for `lake exe lint-style`. -/
-- so far, no help options or so: perhaps that is fine?
def lintStyle : Cmd := `[Cli|
  «lint-style» VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in Mathlib/, Archive/ and Counterexamples/.
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    fix;        "Automatically fix the style error, if possible"
]

/-- The entry point to the `lake exe lint-style` command. -/
def main (args : List String) : IO UInt32 := do lintStyle.validate args
