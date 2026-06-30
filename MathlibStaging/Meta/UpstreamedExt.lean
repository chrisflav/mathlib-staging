module

public import Lean.Environment
public import Lean.EnvExtension
public import Lean.CoreM

/-!
# The `@[upstreamed]` tag store

The non-`meta` environment extension backing the `@[upstreamed]` attribute (see
`MathlibStaging.Meta.Upstreamed`), together with its reader and writer.

These are kept `meta`-free, and separate from the attribute itself, so that the
standalone `upstream` executable can read the recorded tags from a loaded
environment at runtime — runtime code cannot reference `meta` declarations, and
the attribute registration must be `meta` to be active during elaboration.
-/

open Lean

namespace MathlibStaging

/-- The persistent record of `@[upstreamed]` tags: pairs of a tagged declaration
and the mathlib pull request number upstreaming it. -/
public initialize upstreamedExt :
    SimplePersistentEnvExtension (Name × Nat) (Array (Name × Nat)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s e => s.push e
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

/-- If `declName` carries an `@[upstreamed N]` attribute, returns the mathlib pull
request number `N` it is being upstreamed in. -/
public def getUpstreamedPR? (env : Environment) (declName : Name) : Option Nat :=
  (upstreamedExt.getState env).find? (·.1 == declName) |>.map (·.2)

/-- Record that `declName` is being upstreamed in pull request `pr`. The
(`meta`) attribute handler writes to the extension by calling this. -/
public def recordUpstreamed (declName : Name) (pr : Nat) : CoreM Unit :=
  modifyEnv (upstreamedExt.addEntry · (declName, pr))

end MathlibStaging
