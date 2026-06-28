module

public meta import Lean.Elab.Command

/-!
# The `@[overrides]` attribute

Sometimes a declaration from upstream (mathlib) needs to be modified in the staging
library, for example to remove a hypothesis. Since the modified declaration cannot
reuse the upstream name, it is given a primed name (e.g. `foo'`). The `@[overrides]`
attribute records the link between the modified declaration and the upstream one it
replaces, together with a short explanation of what was changed, so that both are
available when upstreaming.

```
@[overrides foo "drops the unused `Nontrivial` hypothesis"]
theorem foo' ... := ...
```

records that `foo'` overrides `foo` and why. The attribute fails if

* `foo` does not exist;
* the explanation string is empty;
* `foo'` would override itself (`foo` and `foo'` resolve to the same declaration);
* `foo'` and `foo` are indistinguishable, i.e. their type signatures are
  definitionally equal (and, for definitions, their bodies are too). In that case
  the modification is a no-op and the primed copy is unnecessary, so an override
  should not be recorded.

The recorded target can be queried with `MathlibStaging.getOverridden?`, and the
full record (target and explanation) with `MathlibStaging.overridesAttr`.
-/

meta section

open Lean Meta Elab

namespace MathlibStaging

/-- The information recorded by the `@[overrides]` attribute on a declaration: the
upstream declaration it overrides and a human-readable explanation of what was
changed in comparison to it. -/
public structure OverrideInfo where
  /-- The upstream declaration that the annotated declaration overrides. -/
  original : Name
  /-- A short explanation of what was changed in comparison to `original`. -/
  changes : String
  deriving Inhabited

/-- Whether `decl` is indistinguishable from `orig`: their type signatures are
definitionally equal and, in the case where both are definitions, so are their
bodies. This is the condition under which `@[overrides]` is rejected, because the
primed copy then does not actually change anything. -/
def isIndistinguishableFrom (decl orig : ConstantInfo) : MetaM Bool := do
  -- Differing universe arities already make the two declarations distinguishable.
  unless decl.levelParams.length == orig.levelParams.length do return false
  let lvls := decl.levelParams.map mkLevelParam
  unless ← isDefEq decl.type (orig.instantiateTypeLevelParams lvls) do return false
  -- Only definitions carry a body worth comparing; for theorems the statement is
  -- all that matters (proofs are irrelevant), and other constants have no body.
  match decl, orig with
  | .defnInfo d, .defnInfo o =>
    isDefEq d.value (o.value.instantiateLevelParams o.levelParams lvls)
  | _, _ => return true

/-- The `@[overrides foo "explanation"]` attribute records that the annotated
declaration is a modified copy of the existing declaration `foo`, intended to
replace it when upstreaming, together with an explanation of what was changed in
comparison to `foo`. See the module doc-string for the failure conditions. -/
syntax (name := overrides) "overrides" ppSpace ident ppSpace str : attr

/-- The `@[overrides foo "explanation"]` attribute. See the module doc-string. -/
public initialize overridesAttr : ParametricAttribute OverrideInfo ←
  registerParametricAttribute {
    name := `overrides
    descr := "record that this declaration is a modified copy of an existing one, \
      together with what was changed, to be reconciled when upstreaming"
    getParam := fun declName stx => do
      let `(attr| overrides $origStx:ident $changesStx:str) := stx
        | throwError "`@[overrides]`: expected `@[overrides foo \"explanation\"]`"
      let changes := changesStx.getString
      if changes.all (·.isWhitespace) then
        throwError "`@[overrides]`: provide a non-empty explanation of what was changed \
          in comparison to the upstream declaration"
      let decl ← getConstInfo declName
      let origName ← realizeGlobalConstNoOverloadWithInfo origStx
      if declName == origName then
        throwError "`@[overrides]`: a declaration cannot override itself"
      let orig ← getConstInfo origName
      if ← (isIndistinguishableFrom decl orig).run' then
        throwError "`@[overrides {.ofConstName origName}]` is unnecessary: \
          `{.ofConstName declName}` is definitionally indistinguishable from \
          `{.ofConstName origName}`, so the modified copy serves no purpose.\n\
          Either modify `{.ofConstName declName}` so that it actually differs from \
          `{.ofConstName origName}`, or drop the primed copy and use \
          `{.ofConstName origName}` directly."
      return { original := origName, changes }
  }

/-- If `declName` carries an `@[overrides foo "explanation"]` attribute, returns the
existing declaration `foo` that it overrides. -/
public def getOverridden? (env : Environment) (declName : Name) : Option Name :=
  (overridesAttr.getParam? env declName).map (·.original)

end MathlibStaging
