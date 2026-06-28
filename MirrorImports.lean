import Lean.Util.Path
import Lean.Elab.ParseImportsFast

/-!
# The `mirror_imports` linter

`mathlib-staging` mirrors the directory and file structure of mathlib: the file
`MathlibStaging/A/B.lean` is the *mirror* of `Mathlib/A/B.lean`.

This executable enforces two things.

**The Init requirement.** Every staging file must import `MathlibStaging.Init`,
directly or transitively. That module registers the staging syntax linters (see
`MathlibStaging.Linter.Staging`), so requiring it everywhere is what makes those
linters run on every staging file.

**The import policy.** If a mirror file's upstream counterpart already exists in
mathlib, then the mirror file may only import

* its own upstream counterpart (`Mathlib.A.B`),
* other mirror files `MathlibStaging.X` whose upstream counterpart `Mathlib.X`
  is a direct import of the upstream file `Mathlib.A.B`, and
* `MathlibStaging.Init`.

Everything that the upstream file pulls in from outside mathlib (`Batteries`,
`Lean`, `Init`, …) is already available through the upstream counterpart, so
mirror files never need to import it directly.

Mirror files without an upstream counterpart (i.e. genuinely new content) are
unrestricted by the import policy, but must still import `MathlibStaging.Init`.

The staging infrastructure modules (`MathlibStaging.Init` itself and everything
under `MathlibStaging.Linter`) are exempt from both checks.

**The aggregator file.** It also checks that the library root `MathlibStaging.lean`
is up to date, i.e. that `lake exe mk_all --lib MathlibStaging --check` would
return `0`: the root must contain one `import` line per module.

Run with `lake exe mirror_imports`. The staging and mathlib source directories
may be overridden as the first two positional arguments (used by the tests).
-/

open Lean System

namespace MirrorImports

/-- Root module name of the mirror hierarchy. -/
def stagingRoot : Name := `MathlibStaging

/-- Root module name of the upstream mathlib hierarchy. -/
def mathlibRoot : Name := `Mathlib

/-- The staging prelude that every staging file must import (transitively). -/
def initModule : Name := `MathlibStaging.Init

/-- Whether `mod` is a staging infrastructure module (the prelude or a linter
definition), which is exempt from the import policy and the Init requirement. -/
def isInfraModule (mod : Name) : Bool :=
  mod == initModule || (`MathlibStaging.Linter).isPrefixOf mod

/-- The string components of a name, root first; `none` if `n` has a numeric
component (which never occurs in module names). -/
def strComponents : Name → Option (List String)
  | .anonymous => some []
  | .str p s => (· ++ [s]) <$> strComponents p
  | .num .. => none

/-- Rebuild a name from its string components, root first. -/
def ofStrComponents (cs : List String) : Name :=
  cs.foldl Name.str Name.anonymous

/-- If the leftmost components of `n` are `oldRoot`, return `n` with that prefix
replaced by `newRoot`; otherwise `none`. Both roots may be multi-component. -/
def reroot (oldRoot newRoot n : Name) : Option Name := do
  let cs ← strComponents n
  let oc ← strComponents oldRoot
  let nc ← strComponents newRoot
  if cs.take oc.length == oc then
    some <| ofStrComponents (nc ++ cs.drop oc.length)
  else
    none

/-- The direct imports of the Lean source file at `path`, omitting `Init`. -/
def fileImports (path : FilePath) : IO (Array Name) := do
  let header ← parseImports' (← IO.FS.readFile path) path.toString
  return header.imports.map (·.module) |>.filter (· != `Init)

/-- Configuration: the directories holding the staging and mathlib sources. -/
structure Config where
  /-- Directory of the mirror hierarchy (root module `MathlibStaging`). -/
  stagingDir : FilePath := "MathlibStaging"
  /-- Directory holding the mathlib sources (parent of the `Mathlib` folder). -/
  mathlibDir : FilePath := ".lake" / "packages" / "mathlib"

/-- Collect every `.lean` file under `dir`, pairing it with the module name
obtained by extending `prefixName` with the relative path. -/
partial def collectModules (dir : FilePath) (prefixName : Name) :
    IO (Array (Name × FilePath)) := do
  let mut out := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      out := out ++ (← collectModules entry.path (prefixName.str entry.fileName))
    else if entry.path.extension == some "lean" then
      let stem := entry.path.fileStem.getD entry.fileName
      out := out.push (prefixName.str stem, entry.path)
  return out

/-- The imports a mirror file of `upstream` is allowed to have: the upstream
counterpart itself, the mirror of every mathlib-rooted direct import of the
upstream file, and the staging prelude. -/
def allowedImports (upstream : Name) (upstreamImports : Array Name) :
    Array Name := Id.run do
  let mut allowed := #[upstream, initModule]
  for imp in upstreamImports do
    if let some mirror := reroot mathlibRoot stagingRoot imp then
      allowed := allowed.push mirror
  return allowed

/-- The content `lake exe mk_all` generates for the aggregator file: one sorted
`import` line per module, in plain (non-`module`) style. This mirrors mathlib's
`mk_all` for a downstream library. -/
def mkAllContent (modules : Array Name) : String :=
  let imports := (modules.map (·.toString)).qsort (· < ·)
  String.intercalate "\n" (imports.map ("import " ++ ·)).toList ++ "\n"

/-- Check that the library root aggregator file is up to date, i.e. that
`mk_all --check` would return `0`: its content must list an `import` for every
module. Returns `true` iff it is up to date. -/
def checkMkAll (cfg : Config) (modules : Array Name) : IO Bool := do
  let rootPath := cfg.stagingDir.addExtension "lean"
  let expected := mkAllContent modules
  let actual ← if (← rootPath.pathExists) then IO.FS.readFile rootPath else pure ""
  if actual == expected then return true
  IO.eprintln s!"error: {rootPath} is out of date; \
    run `lake exe mk_all --lib MathlibStaging` to regenerate it."
  return false

/-- The set of modules that import `MathlibStaging.Init` transitively, given the
direct imports of every staging module. -/
def reachingInit (importsOf : Array (Name × Array Name)) : Array Name := Id.run do
  let mut reach := #[initModule]
  let mut changed := true
  while changed do
    changed := false
    for (mod, imps) in importsOf do
      if !reach.contains mod && imps.any reach.contains then
        reach := reach.push mod
        changed := true
  return reach

/-- Check every staging file against the Init requirement and the import policy,
printing a message for each violation. Returns `true` iff none were found. -/
def check (cfg : Config) : IO Bool := do
  let modules ← collectModules cfg.stagingDir stagingRoot
  -- The path and direct imports of every staging module.
  let mut importsOf := #[]
  for (mod, path) in modules do
    importsOf := importsOf.push (mod, path, ← fileImports path)
  let reach := reachingInit (importsOf.map fun (mod, _, imports) => (mod, imports))
  let mut ok := true
  for (mod, path, imports) in importsOf do
    -- Infrastructure modules are exempt from both checks.
    if isInfraModule mod then continue
    -- (1) The Init requirement.
    unless reach.contains mod do
      ok := false
      IO.eprintln s!"error: {path}: must import `{initModule}` (directly or transitively)."
    -- (2) The import policy, when an upstream counterpart exists.
    let some upstream := reroot stagingRoot mathlibRoot mod | continue
    let upstreamPath := modToFilePath cfg.mathlibDir upstream "lean"
    unless (← upstreamPath.pathExists) do continue
    let allowed := allowedImports upstream (← fileImports upstreamPath)
    for imp in imports do
      unless allowed.contains imp do
        ok := false
        IO.eprintln s!"error: {path}: disallowed import '{imp}'.\n\
          The mirror of '{upstream}' may only import '{upstream}', `{initModule}`, and the \
          mirror-hierarchy counterparts of its direct imports.\n\
          Allowed imports: {allowed.qsort (·.toString < ·.toString) |>.toList}"
  -- The aggregator file must be up to date (`mk_all --check`).
  let mkAllOk ← checkMkAll cfg (importsOf.map fun (mod, _, _) => mod)
  return ok && mkAllOk

end MirrorImports

open MirrorImports in
/-- Entry point: `mirror_imports [stagingDir [mathlibDir]]`. -/
def main (args : List String) : IO UInt32 := do
  let cfg : Config := match args with
    | [] => {}
    | [s] => { stagingDir := s }
    | s :: m :: _ => { stagingDir := s, mathlibDir := m }
  if (← check cfg) then
    IO.println "mirror_imports: all mirror files satisfy the import policy"
    return 0
  else
    IO.eprintln "mirror_imports: import policy violations found"
    return 1
