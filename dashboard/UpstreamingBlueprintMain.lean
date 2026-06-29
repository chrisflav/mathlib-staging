import VersoManual
import VersoBlueprint.PreviewManifest
import UpstreamingBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc UpstreamingBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
