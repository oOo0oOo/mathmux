import Lean.Language.Lean
import Lean.Setup

open Lean Lean.Elab

structure Request where
  source : String
  version : Nat
deriving FromJson

structure Diagnostic where
  severity : String
  kind : String
  text : String
deriving ToJson

structure Response where
  ok : Bool
  diagnostics : Array Diagnostic
  version : Nat
deriving ToJson

def setupImports (setup : ModuleSetup) (profile : Bool) (stx : HeaderSyntax) :
    Language.ProcessingT IO
      (Except Language.Lean.HeaderProcessedSnapshot Language.Lean.SetupImportsResult) := do
  let header := stx.toModuleHeader
  let opts := if profile then
    profiler.set setup.options.toOptions true
  else setup.options.toOptions
  return .ok {
    mainModuleName := setup.name
    isModule := setup.isModule || header.isModule
    imports := setup.imports?.getD header.imports
    opts := Elab.async.setIfNotSet opts true
    importArts := setup.importArts
    plugins := setup.plugins
  }

partial def collectTree (tree : Language.SnapshotTree) : BaseIO MessageLog := do
  let mut messages := tree.element.diagnostics.msgLog
  for child in tree.children do
    messages := messages ++ (← collectTree child.get)
  return messages

def cancelCommandWork (command : Language.Lean.CommandParsedSnapshot) : BaseIO Unit := do
  command.elabSnap.elabSnap.cancelRec
  command.elabSnap.infoTreeSnap.cancelRec
  command.elabSnap.reportSnap.cancelRec

def postErrorIdleMs : Nat := 300
def postErrorMaxMs : Nat := 750
def postErrorFailingCommands : Nat := 3
def postErrorCommandLimit : Nat := 64

/-- Harvest nearby diagnostics without waiting for the remainder of the file. -/
partial def collectAfterError
    (task : Language.SnapshotTask Language.Lean.CommandParsedSnapshot)
    (messages : MessageLog) (failingCommands inspected : Nat)
    (started lastProgress : Nat) : BaseIO MessageLog := do
  if failingCommands >= postErrorFailingCommands || inspected >= postErrorCommandLimit then
    task.cancelRec
    return messages
  let now ← IO.monoMsNow
  if now - started >= postErrorMaxMs || now - lastProgress >= postErrorIdleMs then
    task.cancelRec
    return messages
  let some command ← task.get? | do
    IO.sleep 10
    collectAfterError task messages failingCommands inspected started lastProgress
  let some result ← command.elabSnap.resultSnap.get? | do
    IO.sleep 10
    collectAfterError task messages failingCommands inspected started lastProgress
  cancelCommandWork command
  let commandMessages := result.cmdState.messages
  let messages := messages ++ commandMessages
  let failingCommands := failingCommands + if commandMessages.hasErrors then 1 else 0
  let now ← IO.monoMsNow
  if let some next := command.nextCmdSnap? then
    collectAfterError next messages failingCommands (inspected + 1) started now
  else
    return messages

partial def firstErrorOrFinal (task : Language.SnapshotTask Language.Lean.CommandParsedSnapshot) :
    BaseIO (Bool × MessageLog) := do
  let command := task.get
  let result := command.elabSnap.resultSnap.get
  if result.cmdState.messages.hasErrors then
    cancelCommandWork command
    let messages := result.cmdState.messages
    if let some next := command.nextCmdSnap? then
      let started ← IO.monoMsNow
      let messages ← collectAfterError next messages 1 0 started started
      return (true, messages)
    else
      return (true, messages)
  if let some next := command.nextCmdSnap? then
    firstErrorOrFinal next
  else
    return (false, result.cmdState.messages)

def renderMessages (messages : MessageLog) : BaseIO (Array Diagnostic) := do
  let mut diagnostics := #[]
  for message in messages.reportedPlusUnreported do
    diagnostics := diagnostics.push {
      severity := message.severity.toString
      kind := message.kind.toString
      text := ← message.toString
    }
  return diagnostics

def failureResponse (detail : String) (version : Nat) : Response :=
  { ok := false,
    diagnostics := #[{ severity := "error", kind := "mathmux", text := detail }],
    version := version }

def processSnapshot (snapshot : Language.Lean.InitialSnapshot) (version : Nat) : BaseIO Response := do
  let some header := snapshot.result? |
    return ← failureWithDiagnostics snapshot "header parsing failed" version
  let processed := header.processedSnap.get
  let some processed := processed.result? |
    return ← failureWithDiagnostics snapshot "import processing failed" version
  let (failed, commandMessages) ← firstErrorOrFinal processed.firstCmdSnap
  let messages ← if failed then pure commandMessages else collectTree (Language.toSnapshotTree snapshot)
  let diagnostics ← renderMessages messages
  return { ok := !messages.hasErrors, diagnostics, version := version }

where
  failureWithDiagnostics (snapshot : Language.Lean.InitialSnapshot) (detail : String)
      (version : Nat) : BaseIO Response := do
    let messages ← collectTree (Language.toSnapshotTree snapshot)
    let diagnostics ← renderMessages messages
    if diagnostics.isEmpty then
      return failureResponse detail version
    return { ok := false, diagnostics, version := version }

def writeResponse (response : Response) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn (toJson response).compress
  stdout.flush

unsafe def runServer (setup : ModuleSetup) (profile : Bool) : IO Unit := do
  enableInitializersExecution
  setup.dynlibs.forM loadDynlib
  let processor ← Language.mkIncrementalProcessor (Language.Lean.process (setupImports setup profile))
  let stdin ← IO.getStdin
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return
    if line.trimAscii.isEmpty then loop else
    match Json.parse line >>= fromJson? with
    | .error error =>
      writeResponse (failureResponse error 0)
      loop
    | .ok (request : Request) =>
      enableInitializersExecution
      let input := Parser.mkInputContext request.source setup.name.toString
      let snapshot ← if profile then
        let fresh ← Language.mkIncrementalProcessor (Language.Lean.process (setupImports setup true))
        fresh input
      else
        processor input
      let response ← processSnapshot snapshot request.version
      if profile then Lean.displayCumulativeProfilingTimes
      writeResponse response
      loop
  loop

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | [setupPath] => runServer (← ModuleSetup.load setupPath) false; return 0
  | [setupPath, "--profile"] => runServer (← ModuleSetup.load setupPath) true; return 0
  | _ => IO.eprintln "usage: MathmuxWorker SETUP_JSON [--profile]"; return 2
