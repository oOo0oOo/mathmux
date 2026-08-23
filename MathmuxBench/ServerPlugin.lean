import Lean.Server
import Lean.Server.FileWorker.Utils
import Lean.Server.Requests

open Lean Lean.Lsp Lean.Server

structure CompleteDiagnosticsParams where
  textDocument : TextDocumentIdentifier
  version : Nat
deriving FromJson, ToJson

instance : FileSource CompleteDiagnosticsParams where
  fileSource p := p.textDocument.uri

open RequestM in
partial def handleCompleteDiagnostics (p : CompleteDiagnosticsParams) :
    RequestM (RequestTask (Array Diagnostic)) := do
  let rec waitLoop : RequestM FileWorker.EditableDocument := do
    let doc ← readDoc
    if p.version ≤ doc.meta.version then
      return doc
    else
      IO.sleep 10
      waitLoop
  let task ← RequestM.asTask waitLoop
  RequestM.bindTaskCheap task fun doc? => do
    let doc ← liftExcept doc?
    let complete := doc.reporter.bindCheap (fun _ => doc.cmdSnaps.waitAll)
    RequestM.bindTaskCheap complete fun _ => do
      let diagnostics ← doc.collectCurrentDiagnostics.toIO
      pure <| .pure <| PersistentArray.toArray diagnostics |>.map
        (fun diagnostic => diagnostic.toDiagnostic)

initialize
  registerLspRequestHandler
    "$/mathmux/completeDiagnostics"
    CompleteDiagnosticsParams
    (Array Diagnostic)
    handleCompleteDiagnostics
