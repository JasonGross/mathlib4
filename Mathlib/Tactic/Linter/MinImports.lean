/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import ImportGraph.Imports

/-! # The `minImports` linter

The `minImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, providing information that it better suited, for instance, to split
files.
-/

open Lean Elab Command

namespace Mathlib.MinImports

/-- `getSyntaxNodeKinds stx` takes a `Syntax` input `stx` and returns the `NameSet` of all the
`SyntaxNodeKinds` and all the identifiers contained in `stx`. -/
partial
def getSyntaxNodeKinds : Syntax → NameSet
  | .node _ kind args =>
    ((args.map getSyntaxNodeKinds).foldl (NameSet.append · ·) {}).insert kind
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

/-- extracts the names of the declarations in `env` on which `decl` depends. -/
-- source:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Counting.20prerequisites.20of.20a.20theorem/near/425370265
def getVisited (env : Environment) (decl : Name) : NameSet :=
  let (_, { visited, .. }) := CollectAxioms.collect decl |>.run env |>.run {}
  visited

/-- `getId stx` takes as input a `Syntax` `stx`.
If `stx` contains a `declId`, then it returns the `ident`-syntax for the `declId`.
If `stx` is a nameless instance, then it also tries to fetch the `ident` for the instance.
Otherwise it returns `stx` itself. -/
def getId (stx : Syntax) : CommandElabM Syntax := do
  match stx.find? (·.isOfKind ``Lean.Parser.Command.declId) with
    | some declId => return declId[0]
    | none =>
      match stx.find? (·.isOfKind ``Lean.Parser.Command.instance) with
                | none => return stx
                | some stx => do
                  let dv ← mkDefViewOfInstance {} stx
                  return dv.declId[0]

/-- extract all identifiers, as a `NameSet`. -/
partial
def getIds : Syntax → NameSet
  | .node _ _ args => (args.map getIds).foldl (·.append ·) {}
  | .ident _ _ nm _ => NameSet.empty.insert nm
  | _ => {}

/-- misses `simp`, `ext`, `to_additive`.  Catches `fun_prop`... -/
def getAttrNames (stx : Syntax) : NameSet :=
  match stx.find? (·.isOfKind ``Lean.Parser.Term.attributes) with
    | none => {}
    | some stx => getIds stx

/-- returns all attribute declaration names -/
def getAttrs (env : Environment) (stx : Syntax) : NameSet :=
  Id.run do
  let mut new : NameSet := {}
  for attr in (getAttrNames stx) do --.filterMap fun attr =>
    match getAttributeImpl env attr with
      | .ok attr => new := new.insert attr.ref
      | .error .. => pure ()
  return new

/--`getAllImports cmd` takes a `Syntax` input `cmd` and returns the `NameSet` of all the
module names that are implied by
* the `SyntaxNodeKinds`,
* the attributes of `cmd` (if there are any),
* the identifiers contained in `cmd`,
* if `cmd` adds a declaration `d` to the environment, then also all the module names implied by `d`.
-/
def getAllImports (cmd : Syntax) (dbg? : Bool := false) : CommandElabM NameSet := do
  let env ← getEnv
  --let nm ← liftCoreM do realizeGlobalConstNoOverloadWithInfo (getId cmd)
  -- we put together the implied declaration names, the `SyntaxNodeKinds`, the attributes
  let ts := getVisited env (← getId cmd).getId
              |>.append (getSyntaxNodeKinds cmd)
              |>.append (getAttrs env cmd)
  if dbg? then dbg_trace "{ts.toArray.qsort Name.lt}"
  let mut hm : HashMap Nat Name := {}
  for imp in env.header.moduleNames do
    hm := hm.insert ((env.getModuleIdx? imp).getD default) imp
  let mut fins : NameSet := {}
  for t1 in ts do
    let tns := t1::(← resolveGlobalName t1).map Prod.fst
    for t in tns do
      let new := match env.getModuleIdxFor? t with
        | some t => (hm.find? t).get!
        | none   => default --getMainModule
        if !fins.contains new then fins := fins.insert new
  return fins.erase .anonymous

/-- `getIrredundantImports env importNames` takes an `Environment` and a `NameSet` as inputs.
Assuming that `importNames` are module names,
it returns the `NameSet` consisting of a minimal collection of module names whose transitive
closure is enough to parse (and elaborate) `cmd`. -/
def getIrredundantImports (env : Environment) (importNames : NameSet) : NameSet :=
  importNames.diff (env.findRedundantImports importNames.toArray)

end Mathlib.MinImports

/-!
#  The "minImports" linter

The "minImports" linter tracks information about minimal imports over several commands.
-/

namespace Mathlib.Linter

/-- `minImportsRef` keeps track of cumulative imports across multiple commands. -/
initialize minImportsRef : IO.Ref NameSet ← IO.mkRef {}

/-- `#reset_min_imports` sets to empty the current list of cumulative imports. -/
elab "#reset_min_imports" : command => minImportsRef.set {}

/--
The `minImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, providing information that it better suited, for instance, to split
files.
 -/
register_option linter.minImports : Bool := {
  defValue := true
  descr := "enable the minImports linter"
}

namespace MinImports

open Mathlib.MinImports

/-- Gets the value of the `linter.minImports` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.minImports o

@[inherit_doc Mathlib.Linter.linter.minImports]
def minImportsLinter : Linter where run := withSetOptionIn fun stx => do
    unless linter.minImports.get (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let prevImports ← minImportsRef.get
    if stx.isOfKind ``Parser.Command.eoi then
      let currImps := (((← getEnv).imports.map (·.module)).qsort Name.lt).erase `Init
      if prevImports.toArray.qsort Name.lt != currImps then
        logInfo m!"{currImps}"
    let newImports := getIrredundantImports (← getEnv) (← getAllImports stx)
    let tot := (newImports.append prevImports) --.erase `Lean.Parser.Command
    let redundant := (← getEnv).findRedundantImports tot.toArray
    let currImports := tot.diff redundant
    let currImpArray := currImports.toArray.qsort Name.lt
    if currImpArray != #[] &&
       currImpArray ≠ prevImports.toArray.qsort Name.lt then
      minImportsRef.modify fun _ => currImports
      Linter.logLint linter.minImports stx
        m!"Imports increased to\n{currImpArray}"

initialize addLinter minImportsLinter

end MinImports
