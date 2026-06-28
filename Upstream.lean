module

public import Cli.Basic
import ImportGraph.Imports.RequiredModules
import ImportGraph.Lean.Environment
import Lean.DeclarationRange
import Lean.Data.Json
import Lean.Util.Path

/-!
# `lake exe upstream report`

First component of the upstreaming toolkit. Reports MathlibStaging *units* —
whole files (modules) or individual declarations — ranked by how ready they are
to be upstreamed to mathlib.

For each unit we look only at its **staging-internal** dependencies: edges to
mathlib / Lean / Batteries are ignored, because those are already upstream. Over
that staging-only graph we compute

* **depth** — the longest path to a leaf. A unit with no staging dependencies has
  depth `0` and is *directly upstreamable*; a unit depending only on depth-`0`
  units has depth `1`, and so on.
* **deps** — the number of staging units it transitively depends on.

Filter with `--max-depth N` (e.g. `--max-depth 0` for the directly-upstreamable
worklist) and `--max-deps N`; use `--decls` for declaration granularity and
`--json` for machine-readable output.

Staging *infrastructure* modules (`MathlibStaging.Init`, `MathlibStaging.Linter.*`,
`MathlibStaging.Meta.*`) and the aggregator root are not upstreaming targets and
are excluded.

Caveat: declaration dependencies are computed from `getUsedConstantsAsSet`, which
does not see constants used only through tactics or syntax, so the declaration
graph is a slight under-approximation.
-/

open Lean Core System Cli

namespace Upstream

/-- Root of the staging hierarchy. -/
def stagingRoot : Name := `MathlibStaging

/-- Whether `mod` is a staging infrastructure module (the prelude, the linters or
the meta modules). Mirrors `MirrorImports.isInfraModule`; such modules are not
upstreaming targets. -/
def isInfraModule (mod : Name) : Bool :=
  mod == `MathlibStaging.Init
    || (`MathlibStaging.Linter).isPrefixOf mod
    || (`MathlibStaging.Meta).isPrefixOf mod

/-- Whether `mod` is a staging *content* module: under `MathlibStaging`, not the
aggregator root, and not infrastructure. These are the upstreaming targets. -/
def isContentModule (mod : Name) : Bool :=
  stagingRoot.isPrefixOf mod && mod != stagingRoot && !isInfraModule mod

/-- Union of two `NameSet`s. -/
def nsUnion (a b : NameSet) : NameSet := b.foldl (init := a) fun acc n => acc.insert n

/-- Per-unit metrics over the staging-internal dependency graph. -/
structure Metrics where
  /-- Longest path to a leaf (`0` = no staging dependencies). -/
  depth : Nat
  /-- The staging units transitively depended on (excluding the unit itself). -/
  trans : NameSet

instance : Inhabited Metrics := ⟨{ depth := 0, trans := {} }⟩

/-- Memoized depth and transitive-dependency set of `n` in `graph` (a node → its
direct dependencies, all within the node set). `visiting` guards against cycles
(e.g. mutual declarations); a back-edge into the current path contributes
nothing. -/
partial def metricOf (graph : NameMap (Array Name)) (visiting : NameSet) (n : Name) :
    StateM (NameMap Metrics) Metrics := do
  if let some m := (← get).find? n then
    return m
  if visiting.contains n then
    return { depth := 0, trans := {} }
  let visiting := visiting.insert n
  let mut depth := 0
  let mut trans : NameSet := {}
  for d in (graph.find? n).getD #[] do
    let md ← metricOf graph visiting d
    depth := Nat.max depth (md.depth + 1)
    trans := nsUnion (trans.insert d) md.trans
  let m := { depth, trans }
  modify (·.insert n m)
  return m

/-- Compute metrics for every node of `graph`. -/
def allMetrics (graph : NameMap (Array Name)) : NameMap Metrics := Id.run do
  let mut st : NameMap Metrics := {}
  for (n, _) in graph do
    st := (metricOf graph {} n |>.run st).2
  return st

/-- A reported row: a unit with its defining module and metrics. -/
structure Row where
  /-- The unit's name (module name for files, declaration name for declarations). -/
  name : Name
  /-- The module the unit lives in (equals `name` for files). -/
  module : Name
  /-- Dependency depth. -/
  depth : Nat
  /-- Number of transitive staging dependencies. -/
  deps : Nat

/-- The direct import graph of every loaded module, built from module headers
(robust, independent of which module is "main"). -/
def fileImportGraph (env : Environment) : NameMap (Array Name) := Id.run do
  let mut g : NameMap (Array Name) := {}
  for (mod, idx) in env.header.moduleNames.zipIdx do
    g := g.insert mod (env.header.moduleData[idx]!.imports.map (·.module))
  return g

/-- File-level rows: one per staging content module, over the module import graph
restricted to staging content modules. -/
def analyzeFiles (env : Environment) : Array Row := Id.run do
  let graph : NameMap (Array Name) :=
    (fileImportGraph env).filterMap fun n imps =>
      if isContentModule n then some (imps.filter isContentModule) else none
  let metrics := allMetrics graph
  let mut rows := #[]
  for (n, _) in graph do
    let m := (metrics.find? n).getD { depth := 0, trans := {} }
    rows := rows.push { name := n, module := n, depth := m.depth, deps := m.trans.size }
  return rows

/-- Whether `n` is an auto-generated declaration (recursor, constructor,
`noConfusion`, internal machinery, …) rather than a source-written one, and so
should not be reported as an upstreaming unit in its own right. -/
def isGenerated (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n ||
    match env.find? n with
    | some (.recInfo _) | some (.ctorInfo _) => true
    | _ => false

/-- Declaration-level rows: one per source-written declaration in a staging
content module, over the declaration-use graph restricted to such declarations. -/
def analyzeDecls (env : Environment) : CoreM (Array Row) := do
  -- The source-written declarations living in staging content modules.
  let mut nodes : Array Name := #[]
  for (mod, idx) in env.header.moduleNames.zipIdx do
    if isContentModule mod then
      for n in env.header.moduleData[idx]!.constNames do
        -- Keep only source-written declarations: drop compiler machinery
        -- (`.rec`, `.mk`, `.casesOn`, `.noConfusion`, …) and anything without a source range.
        if !isGenerated env n && (← findDeclarationRanges? n).isSome then
          nodes := nodes.push n
  let nodeSet : NameSet := nodes.foldl (init := {}) fun acc n => acc.insert n
  -- Edges: a declaration depends on the staging declarations it uses.
  let mut graph : NameMap (Array Name) := {}
  for n in nodes do
    let mut used := (← getConstInfo n).getUsedConstantsAsSet
    -- A structure/inductive's real dependencies (its field types) live in its
    -- constructors, which are not reported separately; fold them into the type node.
    if let some (.inductInfo val) := env.find? n then
      for ctor in val.ctors do
        used := nsUnion used (← getConstInfo ctor).getUsedConstantsAsSet
    let deps := used.foldl (init := #[]) fun acc e =>
      if e != n && nodeSet.contains e then acc.push e else acc
    graph := graph.insert n deps
  let metrics := allMetrics graph
  let mut rows := #[]
  for n in nodes do
    let m := (metrics.find? n).getD { depth := 0, trans := {} }
    rows := rows.push
      { name := n, module := (env.getModuleFor? n).getD .anonymous, depth := m.depth, deps := m.trans.size }
  return rows

/-- Render an aligned text table. -/
def renderTable (headers : Array String) (rows : Array (Array String)) : String := Id.run do
  let ncol := headers.size
  let mut widths : Array Nat := headers.map String.length
  for r in rows do
    for i in [0:ncol] do
      widths := widths.set! i (Nat.max widths[i]! (r.getD i "").length)
  let renderRow (cells : Array String) : String :=
    String.intercalate "  " <| (List.range ncol).map fun i =>
      let s := cells.getD i ""
      -- Do not pad the final column, to avoid trailing whitespace in the output.
      if i + 1 == ncol then s else s ++ String.ofList (List.replicate (widths[i]! - s.length) ' ')
  let sep : String :=
    String.intercalate "  " <| (List.range ncol).map fun i => String.ofList (List.replicate widths[i]! '-')
  return String.intercalate "\n" (renderRow headers :: sep :: (rows.map renderRow).toList)

/-- The JSON encoding of a row. -/
def rowJson (r : Row) (decls : Bool) : Json :=
  Json.mkObj <|
    [("name", Json.str r.name.toString), ("depth", toJson r.depth), ("transitiveDeps", toJson r.deps)]
      ++ (if decls then [("module", Json.str r.module.toString)] else [])

/-- Filter, sort and render the rows into the final output string. This must run
while the loaded environment is still alive, because `Row` names are region
allocated in the environment's imported data. -/
def formatReport (rows0 : Array Row) (decls : Bool) (maxDepth? maxDeps? : Option Nat)
    (asJson : Bool) : String := Id.run do
  let rows := (rows0.filter fun r => maxDepth?.all (r.depth ≤ ·) && maxDeps?.all (r.deps ≤ ·)).qsort
    fun a b =>
      if a.depth != b.depth then a.depth < b.depth
      else if a.deps != b.deps then a.deps < b.deps
      else a.name.toString < b.name.toString
  if asJson then
    return (Json.arr (rows.map (rowJson · decls))).pretty
  if rows.isEmpty then
    return "(no matching units)"
  let headers := if decls then #["depth", "deps", "declaration", "module"] else #["depth", "deps", "file"]
  let body := rows.map fun r =>
    if decls then #[toString r.depth, toString r.deps, r.name.toString, r.module.toString]
    else #[toString r.depth, toString r.deps, r.name.toString]
  return renderTable headers body ++ s!"\n\n{rows.size} unit(s); depth 0 = directly upstreamable."

/-- Implementation of `lake exe upstream report`. -/
def runReport (p : Parsed) : IO UInt32 := do
  let decls := p.hasFlag "decls"
  let maxDepth? : Option Nat := (p.flag? "max-depth").map (·.as! Nat)
  let maxDeps? : Option Nat := (p.flag? "max-deps").map (·.as! Nat)
  let asJson := p.hasFlag "json"
  initSearchPath (← findSysroot)
  unsafe Lean.enableInitializersExecution
  -- All work that touches environment-owned `Name`s happens inside the closure;
  -- only the finished `String` escapes (the env's imported data is freed on exit).
  let output ← unsafe withImportModules #[{module := stagingRoot}] {} (trustLevel := 1024) fun env => do
    let rows ← if decls then
        let ctx : Core.Context := { options := {}, fileName := "<upstream>", fileMap := default }
        Prod.fst <$> CoreM.toIO (analyzeDecls env) ctx { env }
      else
        pure (analyzeFiles env)
    pure (formatReport rows decls maxDepth? maxDeps? asJson)
  IO.println output
  return 0

/-- `lake exe upstream report` -/
def reportCmd : Cmd := `[Cli|
  report VIA runReport; ["0.1.0"]
  "List MathlibStaging units by upstreaming readiness: dependency depth and \
   number of transitive staging dependencies."

  FLAGS:
    decls;             "Report individual declarations instead of whole files."
    "max-depth" : Nat; "Only show units with dependency depth ≤ N (0 = directly upstreamable)."
    "max-deps" : Nat;  "Only show units with at most N transitive staging dependencies."
    json;              "Emit JSON instead of an aligned table."
]

/-- The `upstream` command, dispatching to its subcommands. -/
def upstreamCmd : Cmd := `[Cli|
  upstream NOOP; ["0.1.0"]
  "Tooling for upstreaming MathlibStaging content to mathlib."

  SUBCOMMANDS:
    reportCmd
]

end Upstream

/-- `lake exe upstream` -/
public def main (args : List String) : IO UInt32 :=
  Upstream.upstreamCmd.validate args
