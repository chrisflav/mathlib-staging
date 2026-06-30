module

public meta import MathlibStaging.Meta.UpstreamedExt
public meta import Lean.Elab.Command

/-!
# The `@[upstreamed]` attribute

When a declaration in the staging library has been included in a pull request to
mathlib, it is tagged with the number of that pull request:

```
@[upstreamed 12345]
theorem foo' ... := ...
```

records that `foo'` is being upstreamed in mathlib pull request `#12345`. Once
that pull request is merged, the declaration lives in mathlib and can be removed
from the staging library; `lake exe upstream check` finds such declarations by
querying the merge status of the recorded pull requests.

The attribute fails if the pull request number is not positive. The recorded
data lives in `MathlibStaging.upstreamedExt` (see `MathlibStaging.Meta.UpstreamedExt`)
and is queried with `MathlibStaging.getUpstreamedPR?`. The attribute registration
here is `meta` (so it is active during elaboration); it writes to the non-`meta`
extension by calling the non-`meta` `MathlibStaging.recordUpstreamed`.
-/

namespace MathlibStaging

meta section

open Lean Elab

/-- The `@[upstreamed N]` attribute records that the annotated declaration is part
of mathlib pull request `N`, opened to upstream it. See the module doc-string. -/
syntax (name := upstreamed) "upstreamed" ppSpace num : attr

initialize registerBuiltinAttribute {
  name := `upstreamed
  descr := "record that this declaration is being upstreamed to mathlib in the given pull request"
  add := fun decl stx _kind => do
    let `(attr| upstreamed $prStx:num) := stx
      | throwError "`@[upstreamed]`: expected `@[upstreamed <pr-number>]`"
    let pr := prStx.getNat
    if pr == 0 then
      throwError "`@[upstreamed]`: the pull request number must be positive"
    recordUpstreamed decl pr
}

end

end MathlibStaging
