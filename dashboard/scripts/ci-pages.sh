#!/usr/bin/env bash

# Build the Verso upstreaming-dashboard site into `_out/site/html-multi`.
# Assumes `UpstreamingBlueprint/Chapters/Graph.lean` has already been generated
# by `lake exe upstream viz --decls --format verso` in the main repository.

set -euo pipefail

cd "$(dirname "$0")/.."

lake build UpstreamingBlueprint
lake env lean --run UpstreamingBlueprintMain.lean --output _out/site

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
