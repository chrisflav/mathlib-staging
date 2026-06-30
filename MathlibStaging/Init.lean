module

public import MathlibStaging.Linter.Staging
public import MathlibStaging.Meta.Overrides
public import MathlibStaging.Meta.Upstreamed

/-!
# `MathlibStaging.Init`

Every staging file must import this module (directly or transitively); the
`mirror_imports` linter enforces this. Importing it registers the staging syntax
linters (see `MathlibStaging.Linter.Staging`) and the `@[overrides]` and
`@[upstreamed]` attributes (see `MathlibStaging.Meta.Overrides` and
`MathlibStaging.Meta.Upstreamed`) so that they are available on every staging file.

It plays the same role for the staging library that `Mathlib.Init` plays for
mathlib.
-/
