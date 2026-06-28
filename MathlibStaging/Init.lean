import MathlibStaging.Linter.Staging

/-!
# `MathlibStaging.Init`

Every staging file must import this module (directly or transitively); the
`mirror_imports` linter enforces this. Importing it registers the staging syntax
linters (see `MathlibStaging.Linter.Staging`) so that they run on the file.

It plays the same role for the staging library that `Mathlib.Init` plays for
mathlib.
-/
