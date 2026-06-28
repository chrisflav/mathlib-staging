# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Enforce the staging import policy and the `MathlibStaging.Init` requirement.
# This is a fast, source-only check, so run it before the expensive build.
lake exe mirror_imports || exit 1

# Verify all .lean files are imported.
lake exe mk_all --git --check || exit 1

# Fetch build cache
lake exe cache get

# Verify everything builds (the staging syntax linters run during the build).
lake build --wfail || exit 1
