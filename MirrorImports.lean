import Lean.Util.Path
import Lean.Elab.ParseImportsFast

/-!
# The `mirror_imports` linter

`mathlib-staging` mirrors the directory and file structure of mathlib: the file
`MathlibStaging/A/B.lean` is the *mirror* of `Mathlib/A/B.lean`.

This executable enforces three things.

**The Init requirement.** Every staging file must import `MathlibStaging.Init`,
directly or transitively. That module registers the staging syntax linters (see
`MathlibStaging.Linter.Staging`), so requiring it everywhere is what makes those
linters run on every staging file.

**The import policy.** If a mirror file's upstream counterpart already exists in
mathlib, then the mirror file must import that upstream counterpart
(`Mathlib.A.B`), and may otherwise only import

* other mirror files `MathlibStaging.X` whose upstream counterpart `Mathlib.X`
  is a direct import of the upstream file `Mathlib.A.B`, and
* `MathlibStaging.Init`.

Importing the upstream counterpart is required because the mirror builds on it;
everything else that the upstream file pulls in from outside mathlib (`Batteries`,
`Lean`, `Init`, …) is already available through that counterpart, so mirror files
never need to import it directly.

**The module-docstring policy.** If a mirror file's upstream counterpart already
exists in mathlib, then the mirror file may not contain a non-empty module
docstring (`/-! … -/`): the upstream file already documents the module, and the
mirror only adds or adjusts declarations. The docstring must still be present but
empty (mathlib's `linter.style.header` requires every file to open with one), and
documentation for genuinely new material belongs in a docstring on the
declaration it concerns.

Mirror files without an upstream counterpart (i.e. genuinely new content) are
unrestricted by the import and module-docstring policies, but must still import
`MathlibStaging.Init`.

The staging infrastructure modules (`MathlibStaging.Init` itself and everything
under `MathlibStaging.Linter` and `MathlibStaging.Meta`) are exempt from all of
these checks.

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

/-- Whether `mod` is a staging infrastructure module (the prelude, a linter
definition, or a metaprogramming module such as the `@[overrides]` attribute),
which is exempt from the import policy and the Init requirement. These modules are
the ones aggregated by `MathlibStaging.Init`, so they cannot import it without
creating a cycle. -/
def isInfraModule (mod : Name) : Bool :=
  mod == initModule || (`MathlibStaging.Linter).isPrefixOf mod ||
    (`MathlibStaging.Meta).isPrefixOf mod

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

/-! ## Detecting non-empty module docstrings

A *module docstring* is a block comment whose opening delimiter is immediately
followed by a `!`; it documents the file as a whole, unlike an ordinary block
comment or a declaration docstring (whose opening delimiter is followed by a
second `-` instead). The functions below find the non-empty module docstrings in
a source file by a small comment-aware scan, so that the import policy can forbid
them in mirrors of files that already exist upstream. We scan the raw text rather
than running the Lean parser because this executable deliberately avoids
elaborating the staging sources. -/

/-- Advance past a line comment, returning the index just after the next
newline (or the end of input). `i` points just after the opening `--`. -/
partial def skipLineComment (a : Array Char) (i : Nat) : Nat :=
  if i ≥ a.size then i
  else if a[i]! == '\n' then i + 1
  else skipLineComment a (i + 1)

/-- Advance past a string literal, returning the index just after the closing
quote (or the end of input). `i` points just after the opening `"`. -/
partial def skipString (a : Array Char) (i : Nat) : Nat :=
  if i ≥ a.size then i
  else if a[i]! == '\\' then skipString a (i + 2)
  else if a[i]! == '"' then i + 1
  else skipString a (i + 1)

/-- Advance past a block comment, returning the index just after its matching
close. `i` points just after the two-character opener and `depth` is the current
nesting depth (`1` for the comment just opened). Block comments nest but do not
interpret strings or line comments, so only the open and close delimiters are
tracked. -/
partial def skipBlockComment (a : Array Char) (i depth : Nat) : Nat :=
  if i ≥ a.size then i
  else
    let c := a[i]!
    let c1 := if i + 1 < a.size then a[i + 1]! else ' '
    if c == '/' && c1 == '-' then skipBlockComment a (i + 2) (depth + 1)
    else if c == '-' && c1 == '/' then
      if depth == 1 then i + 2 else skipBlockComment a (i + 2) (depth - 1)
    else skipBlockComment a (i + 1) depth

/-- Whether `a` has a non-whitespace character in the half-open range
`[lo, hi)`. -/
partial def hasNonWhitespace (a : Array Char) (lo hi : Nat) : Bool :=
  if lo ≥ hi then false
  else if lo < a.size && !a[lo]!.isWhitespace then true
  else hasNonWhitespace a (lo + 1) hi

/-- Scan `a` from index `i`, collecting the opening index of every *non-empty*
module docstring. String literals, line comments and the interiors of ordinary or
nested block comments are skipped, so a docstring opener appearing inside any of
those is not mistaken for a real module docstring. A docstring counts as non-empty
when it has a non-whitespace character between its opener and its closing
delimiter. -/
partial def scanModuleDocs (a : Array Char) (i : Nat) (acc : Array Nat) : Array Nat :=
  if i ≥ a.size then acc
  else
    let c := a[i]!
    let c1 := if i + 1 < a.size then a[i + 1]! else ' '
    let c2 := if i + 2 < a.size then a[i + 2]! else ' '
    if c == '"' then
      scanModuleDocs a (skipString a (i + 1)) acc
    else if c == '-' && c1 == '-' then
      scanModuleDocs a (skipLineComment a (i + 2)) acc
    else if c == '/' && c1 == '-' && c2 == '!' then
      let stop := skipBlockComment a (i + 2) 1
      -- The content lies between the opening `/-!` (3 chars) and the closing `-/` (2 chars).
      let acc := if hasNonWhitespace a (i + 3) (stop - 2) then acc.push i else acc
      scanModuleDocs a stop acc
    else if c == '/' && c1 == '-' then
      scanModuleDocs a (skipBlockComment a (i + 2) 1) acc
    else
      scanModuleDocs a (i + 1) acc

/-- The 1-based line number of character index `idx` in `a`. -/
partial def lineOf (a : Array Char) (idx : Nat) : Nat := Id.run do
  let mut n := 1
  for k in [0:min idx a.size] do
    if a[k]! == '\n' then n := n + 1
  return n

/-- The 1-based line numbers of the non-empty module docstrings in `src`. -/
def nonEmptyModuleDocLines (src : String) : Array Nat :=
  let a := src.toList.toArray
  (scanModuleDocs a 0 #[]).map (lineOf a)

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
    -- (2a) The mirror must import its upstream counterpart, which it builds on.
    unless imports.contains upstream do
      ok := false
      IO.eprintln s!"error: {path}: must import its upstream counterpart `{upstream}`.\n\
        A mirror of an existing mathlib file builds on that file, so it has to import it."
    -- (2b) The mirror may import nothing beyond the allowed set.
    let allowed := allowedImports upstream (← fileImports upstreamPath)
    for imp in imports do
      unless allowed.contains imp do
        ok := false
        IO.eprintln s!"error: {path}: disallowed import '{imp}'.\n\
          The mirror of '{upstream}' may only import '{upstream}', `{initModule}`, and the \
          mirror-hierarchy counterparts of its direct imports.\n\
          Allowed imports: {allowed.qsort (·.toString < ·.toString) |>.toList}"
    -- (3) The module-docstring policy, when an upstream counterpart exists. The
    -- upstream file already carries the module's documentation, so its mirror
    -- must not repeat it in a non-empty module docstring of its own.
    for line in nonEmptyModuleDocLines (← IO.FS.readFile path) do
      ok := false
      IO.eprintln s!"error: {path}:{line}: non-empty module docstring is not allowed in a mirror \
        of an existing mathlib file.\n\
        The upstream file '{upstream}' already documents this module, so its mirror must not repeat \
        that documentation. Replace it with an empty module docstring — a `/-!` line and a closing \
        `-/` line with nothing in between — rather than deleting it: mathlib's `linter.style.header` \
        still requires every file to open with a module docstring. Put documentation for genuinely \
        new material in a docstring on the declaration it concerns."
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
