module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Command
public meta import Lean.Linter.Basic

/-!
# Staging syntax linters

This file defines the staging library's own syntax linters. They are aggregated
in `MathlibStaging.Init`, which the `mirror_imports` linter requires every
staging file to import (directly or transitively); that is how these linters get
run on every mirror file.

* `linter.staging.heartbeats` forbids modifying `maxHeartbeats` (scoped or not).
* `linter.staging.bannedTactics` forbids the `change` and `erw` tactics.
* `linter.staging.proofLength` limits a proof to a number of non-comment lines.
-/

meta section

open Lean Elab Command Linter

namespace MathlibStaging.Linter

/-- Every subterm of `stx` (including `stx` itself) satisfying `p`, in traversal
order. -/
partial def collectMatching (p : Syntax → Bool) (stx : Syntax) : Array Syntax :=
  let here := if p stx then #[stx] else #[]
  stx.getArgs.foldl (init := here) fun acc arg => acc ++ collectMatching p arg

/-! ## The `heartbeats` linter -/

/-- The `heartbeats` linter forbids any `set_option maxHeartbeats …`, whether at
file scope or scoped to a declaration with `in`. Proofs in the staging library
are expected to work within the default heartbeat budget. -/
public register_option linter.staging.heartbeats : Bool := {
  defValue := true
  descr := "enable the staging linter forbidding `maxHeartbeats` changes"
}

/-- The name of the option set by a `set_option` command/term/tactic `stx`. -/
def parseSetOption : Syntax → Option Name
  | `(command|set_option $name:ident $_val) => some name.getId
  | `(set_option $name:ident $_val in $_x) => some name.getId
  | `(tactic|set_option $name:ident $_val in $_x) => some name.getId
  | _ => none

@[inherit_doc linter.staging.heartbeats]
def heartbeatsLinter : Linter where
  -- We deliberately do not use `withSetOptionIn`: it would peel off (and thus
  -- hide from us) the `set_option maxHeartbeats … in` we want to flag.
  run stx := do
    unless getLinterValue linter.staging.heartbeats (← getLinterOptions) do return
    if (← get).messages.hasErrors then return
    for opt in collectMatching (parseSetOption · |>.isSome) stx do
      if let some name := parseSetOption opt then
        if name.components.contains `maxHeartbeats then
          Linter.logLint linter.staging.heartbeats opt
            m!"Modifying `{name}` is not allowed in the staging library; \
              proofs are expected to work within the default heartbeat budget."

initialize addLinter heartbeatsLinter

/-! ## The `bannedTactics` linter -/

/-- The `bannedTactics` linter forbids the `change` and `erw` tactics. -/
public register_option linter.staging.bannedTactics : Bool := {
  defValue := true
  descr := "enable the staging linter forbidding the `change` and `erw` tactics"
}

/-- The banned tactic keyword `stx` is the atom of, if any. -/
def bannedAtom? (stx : Syntax) : Option String :=
  if stx.isAtom then
    match stx.getAtomVal with
    | "erw" | "erw " => some "erw"
    | "change" | "change " => some "change"
    | _ => none
  else none

@[inherit_doc linter.staging.bannedTactics]
def bannedTacticsLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.staging.bannedTactics (← getLinterOptions) do return
    if (← get).messages.hasErrors then return
    for node in collectMatching (bannedAtom? · |>.isSome) stx do
      if let some keyword := bannedAtom? node then
        Linter.logLint linter.staging.bannedTactics node
          m!"The `{keyword}` tactic is not allowed in the staging library."

initialize addLinter bannedTacticsLinter

/-! ## The `proofLength` linter -/

/-- The `proofLength` linter limits the body of a `theorem`/`lemma`/`example`
(everything from `:=` onwards, comments excluded) to `linter.staging.proofLengthLimit`
lines. -/
public register_option linter.staging.proofLength : Bool := {
  defValue := true
  descr := "enable the staging linter limiting proof length"
}

/-- The maximum number of non-comment lines allowed in a proof body. -/
public register_option linter.staging.proofLengthLimit : Nat := {
  defValue := 100
  descr := "the maximum number of non-comment lines allowed in a proof"
}

/-- Replace every comment and string literal in `a` by spaces, preserving the
line structure, starting in the given lexer state. -/
partial def blankComments (a : Array Char) (i depth : Nat) (lineComment inStr : Bool)
    (out : Array Char) : Array Char :=
  if i ≥ a.size then out else
  let c := a[i]!
  let c2 := if i + 1 < a.size then a[i + 1]! else ' '
  let keep (c : Char) : Char := if c == '\n' then '\n' else ' '
  if lineComment then
    if c == '\n' then blankComments a (i + 1) depth false inStr (out.push '\n')
    else blankComments a (i + 1) depth true inStr (out.push ' ')
  else if depth > 0 then
    if c == '/' && c2 == '-' then blankComments a (i + 2) (depth + 1) false inStr ((out.push ' ').push ' ')
    else if c == '-' && c2 == '/' then blankComments a (i + 2) (depth - 1) false inStr ((out.push ' ').push ' ')
    else blankComments a (i + 1) depth false inStr (out.push (keep c))
  else if inStr then
    if c == '\\' then blankComments a (i + 2) depth false true ((out.push ' ').push (keep c2))
    else if c == '"' then blankComments a (i + 1) depth false false (out.push ' ')
    else blankComments a (i + 1) depth false true (out.push (keep c))
  else
    if c == '"' then blankComments a (i + 1) depth false true (out.push ' ')
    else if c == '/' && c2 == '-' then blankComments a (i + 2) 1 false false ((out.push ' ').push ' ')
    else if c == '-' && c2 == '-' then blankComments a (i + 1) depth true false (out.push ' ')
    else blankComments a (i + 1) depth false inStr (out.push c)

/-- The number of lines of `src` that contain code (not just comments/whitespace). -/
def countCodeLines (src : String) : Nat :=
  let a := src.toList.toArray
  let blanked := String.ofList (blankComments a 0 0 false false (Array.mkEmpty a.size)).toList
  (blanked.splitOn "\n").foldl (init := 0) fun n line =>
    if line.any (!·.isWhitespace) then n + 1 else n

/-- Whether `stx` is a `theorem`, `lemma` or `example` declaration. -/
def isProofDecl (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Command.declaration &&
    let k := stx[1].getKind
    k == ``Lean.Parser.Command.theorem || k == ``Lean.Parser.Command.example ||
      k.components.getLast? == some `lemma

@[inherit_doc linter.staging.proofLength]
def proofLengthLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.staging.proofLength (← getLinterOptions) do return
    if (← get).messages.hasErrors then return
    unless isProofDecl stx do return
    let some declVal := stx.find? (·.isOfKind ``Lean.Parser.Command.declValSimple) | return
    let some startPos := declVal.getPos? | return
    let some endPos := declVal.getTailPos? | return
    let limit := linter.staging.proofLengthLimit.get (← getOptions)
    let length := countCodeLines (String.Pos.Raw.extract (← getFileMap).source startPos endPos)
    if length > limit then
      Linter.logLint linter.staging.proofLength declVal
        m!"This proof is {length} lines long, exceeding the staging limit of {limit} lines."

initialize addLinter proofLengthLinter

end MathlibStaging.Linter
