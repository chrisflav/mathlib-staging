module

public meta import Lean.Elab.Command

/-!
# The `@[overrides]` attribute

Sometimes a declaration from upstream (mathlib) needs to be modified in the staging
library, for example to remove a hypothesis. Since the modified declaration cannot
reuse the upstream name, it is given a primed name (e.g. `foo'`). The `@[overrides]`
attribute records the link between the modified declaration and the upstream one it
replaces, so that the connection is available when upstreaming.

```
@[overrides foo]
theorem foo' ... := ...
```

records that `foo'` overrides `foo`. The attribute fails if

* `foo` does not exist;
* `foo'` would override itself (`foo` and `foo'` resolve to the same declaration);
* `foo'` and `foo` are indistinguishable, i.e. their type signatures are
  definitionally equal (and, for definitions, their bodies are too). In that case
  the modification is a no-op and the primed copy is unnecessary, so an override
  should not be recorded.

The recorded target can be queried with `MathlibStaging.getOverridden?`.
-/

meta section

open Lean Meta Elab

namespace MathlibStaging

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

/-- The `@[overrides foo]` attribute records that the annotated declaration is a
modified copy of the existing declaration `foo`, intended to replace it when
upstreaming. See the module doc-string for the failure conditions. -/
public initialize overridesAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `overrides
    descr := "record that this declaration is a modified copy of an existing one, \
      to be reconciled when upstreaming"
    getParam := fun declName stx => do
      let decl ← getConstInfo declName
      let origName ← realizeGlobalConstNoOverloadWithInfo (← Attribute.Builtin.getIdent stx)
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
      return origName
  }

/-- If `declName` carries an `@[overrides foo]` attribute, returns the existing
declaration `foo` that it overrides. -/
public def getOverridden? (env : Environment) (declName : Name) : Option Name :=
  overridesAttr.getParam? env declName

end MathlibStaging
