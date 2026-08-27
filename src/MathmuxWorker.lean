import Lean.Language.Lean
import Lean.Setup
import Lean.Server.InfoUtils
import Lean.Elab.Tactic

open Lean Lean.Elab

structure Request where
  operation : String
  source : String
  file_name : String
  version : Nat
  line : Nat := 0
  column : Nat := 0
  input : String := ""
deriving FromJson

structure Diagnostic where
  severity : String
  kind : String
  text : String
deriving ToJson

structure ProfileEntry where
  line : Nat
  column : Nat
  kind : String
  detail : String
  duration_ms : Float
deriving ToJson

structure Response where
  ok : Bool
  diagnostics : Array Diagnostic
  profile : Array ProfileEntry := #[]
  detail : String := ""
  version : Nat
deriving ToJson

def goalContext (goal : GoalsAtResult) : ContextInfo :=
  { goal.ctxInfo with
    mctx := if goal.useAfter then goal.tacticInfo.mctxAfter else goal.tacticInfo.mctxBefore }

def goalMVars (goal : GoalsAtResult) : List MVarId :=
  if goal.useAfter then goal.tacticInfo.goalsAfter else goal.tacticInfo.goalsBefore

def goalsBetweenOffsets (trees : Array InfoTree) (fileMap : FileMap)
    (start stop : Nat) :
    Option GoalsAtResult := Id.run do
  for tree in trees do
    for offset in [start:stop + 1] do
      let hover : String.Pos.Raw := ⟨offset⟩
      if let some goal :=
          (tree.goalsAt? fileMap hover).find? fun goal => !(goalMVars goal).isEmpty then
        return some goal
  return none

partial def goalInSnapshotTree (tree : Language.SnapshotTree) (fileMap : FileMap)
    (start stop : Nat) : BaseIO (Option GoalsAtResult) := do
  if let some goal := goalsBetweenOffsets tree.element.infoTree?.toArray fileMap start stop then
    return some goal
  for child in tree.children do
    if let some goal ← goalInSnapshotTree child.get fileMap start stop then
      return some goal
  return none

def goalAtPosition (tree : Language.SnapshotTree) (fileMap : FileMap)
    (line column : Nat) : BaseIO (Option GoalsAtResult) := do
  if line == 0 then return none
  let zeroLine := line - 1
  let start := fileMap.ofPosition {line := zeroLine, column := column - 1}
  if column > 0 then
    return ← goalInSnapshotTree tree fileMap start.byteIdx start.byteIdx
  let stop := fileMap.ofPosition {line := zeroLine + 1, column := 0}
  goalInSnapshotTree tree fileMap start.byteIdx stop.byteIdx

def parseCategory (category : Name) (source : String) : CoreM Syntax := do
  match Parser.runParserCategory (← getEnv) category source with
  | .ok stx => pure stx
  | .error error => throwError error

def inspectTerm (operation source : String) : Term.TermElabM String := do
  let stx ← parseCategory `term source
  if operation == "synth" then
    let type ← Term.elabType stx
    let value ← Meta.synthInstance type
    return s!"{(← Meta.ppExpr value).pretty} : {(← Meta.ppExpr type).pretty}"
  let value ← Term.elabTerm stx none
  if operation == "reduce" then
    return (← Meta.ppExpr (← Meta.reduce value)).pretty
  return s!"{(← Meta.ppExpr value).pretty} : {(← Meta.ppExpr (← Meta.inferType value)).pretty}"

def evalTacticText (source : String) : Tactic.TacticM Unit := do
  let stx ← parseCategory `tactic source
  Tactic.evalTactic stx

def probeFailure (detail : String) (version : Nat) : Response :=
  { ok := false,
    diagnostics := #[{ severity := "error", kind := "mathmux", text := detail }],
    detail,
    version }

def runLocalProbe (snapshot : Language.Lean.InitialSnapshot) (request : Request) : IO Response := do
  let some goal ← goalAtPosition (Language.toSnapshotTree snapshot)
      snapshot.ictx.fileMap request.line request.column
    | return probeFailure s!"no tactic context at line {request.line}" request.version
  let mvars := goalMVars goal
  let ctx := goalContext goal
  try
    let detail ← if request.operation == "goal" then
      pure (← ctx.ppGoals mvars).pretty
    else if request.operation == "tactic" then
      ctx.runMetaM {} do
        let action : Tactic.TacticM String := do
          evalTacticText request.input
          let remaining ← Tactic.getUnsolvedGoals
          if remaining.isEmpty then return "solved"
          let formats ← liftM (m := MetaM) (remaining.mapM Meta.ppGoal)
          return (Std.Format.prefixJoin "\n" formats).pretty
        (((action {elaborator := .anonymous}).run' {goals := mvars}) {}).run' {}
    else
      let some mvar := mvars.head?
        | throw <| IO.userError "probe position has no active goal"
      ctx.runMetaM {} do
        mvar.withContext do
          (inspectTerm request.operation request.input {}).run' {}
    return {ok := true, diagnostics := #[], detail, version := request.version}
  catch error =>
    return probeFailure (toString error) request.version

def setupImports (setup : ModuleSetup) (profile : Bool) (stx : HeaderSyntax) :
    Language.ProcessingT IO
      (Except Language.Lean.HeaderProcessedSnapshot Language.Lean.SetupImportsResult) := do
  let header := stx.toModuleHeader
  let opts := if profile then
    let opts := profiler.set setup.options.toOptions true
    let opts := trace.profiler.set opts true
    let opts := trace.profiler.threshold.set opts 50
    let opts := trace.profiler.output.set opts "mathmux"
    Elab.async.set opts false
  else
    -- A check must report the first error in the current source. With asynchronous
    -- command elaboration, later declarations can expose synthetic unsolved goals
    -- before an earlier tactic failure has reached its snapshot.
    Elab.async.set setup.options.toOptions false
  return .ok {
    mainModuleName := setup.name
    isModule := setup.isModule || header.isModule
    imports := setup.imports?.getD header.imports
    opts
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
  let commandMessages := result.diagnostics.msgLog ++ result.cmdState.messages
  let messages := messages ++ commandMessages
  let failingCommands := failingCommands + if commandMessages.hasErrors then 1 else 0
  let now ← IO.monoMsNow
  if let some next := command.nextCmdSnap? then
    collectAfterError next messages failingCommands (inspected + 1) started now
  else
    return messages

partial def collectTraceProfile (fileMap : FileMap) (ref : Syntax) :
    MessageData → Array ProfileEntry
  | .trace data _ children =>
      let elapsed := (data.stopTime - data.startTime) * 1000
      let children := children.flatMap (collectTraceProfile fileMap ref)
      if elapsed < 5 then children else
        let pos := fileMap.toPosition (ref.getPos?.getD 0)
        let detail := if data.tag.isEmpty then "" else data.tag
        #[{ line := pos.line + 1, column := pos.column + 1, kind := data.cls.toString,
            detail, duration_ms := elapsed }] ++ children
  | .withContext _ msg => collectTraceProfile fileMap ref msg
  | .withNamingContext _ msg => collectTraceProfile fileMap ref msg
  | .nest _ msg => collectTraceProfile fileMap ref msg
  | .group msg => collectTraceProfile fileMap ref msg
  | .compose left right =>
      collectTraceProfile fileMap ref left ++ collectTraceProfile fileMap ref right
  | .tagged _ msg => collectTraceProfile fileMap ref msg
  | .ofOriginatingSyntax origin msg => collectTraceProfile fileMap origin msg
  | _ => #[]

def collectResultProfile (fileMap : FileMap)
    (result : Language.Lean.CommandResultSnapshot) : Array ProfileEntry := Id.run do
  let mut entries := #[]
  for trace in result.traces.traces do
    entries := entries ++ collectTraceProfile fileMap trace.ref trace.msg
  return entries

partial def firstErrorOrFinal (task : Language.SnapshotTask Language.Lean.CommandParsedSnapshot)
    (fileMap : FileMap) (profile : Bool) :
    BaseIO (Bool × MessageLog × Array ProfileEntry) := do
  let command := task.get
  let result := command.elabSnap.resultSnap.get
  let entries := if profile then collectResultProfile fileMap result else #[]
  let messages := result.diagnostics.msgLog ++ result.cmdState.messages
  if messages.hasErrors then
    cancelCommandWork command
    if let some next := command.nextCmdSnap? then
      let started ← IO.monoMsNow
      let messages ← collectAfterError next messages 1 0 started started
      return (true, messages, entries)
    else
      return (true, messages, entries)
  if let some next := command.nextCmdSnap? then
    let (failed, messages, rest) ← firstErrorOrFinal next fileMap profile
    return (failed, messages, entries ++ rest)
  else
    return (false, result.cmdState.messages, entries)

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

def processSnapshot (snapshot : Language.Lean.InitialSnapshot) (version : Nat)
    (profile : Bool) : BaseIO Response := do
  let some header := snapshot.result? |
    return ← failureWithDiagnostics snapshot "header parsing failed" version
  let processed := header.processedSnap.get
  let some processed := processed.result? |
    return ← failureWithDiagnostics snapshot "import processing failed" version
  let (failed, commandMessages, profileEntries) ←
    firstErrorOrFinal processed.firstCmdSnap snapshot.ictx.fileMap profile
  let messages ← if failed then pure commandMessages else collectTree (Language.toSnapshotTree snapshot)
  let diagnostics ← renderMessages messages
  return { ok := !messages.hasErrors, diagnostics, profile := profileEntries, version := version }

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
      let fileName := if setup.name == `_unknown then request.file_name else setup.name.toString
      let input := Parser.mkInputContext request.source fileName
      let snapshot ← if profile then
        let fresh ← Language.mkIncrementalProcessor (Language.Lean.process (setupImports setup true))
        fresh input
      else
        processor input
      let response ← if request.operation == "check" then
        processSnapshot snapshot request.version profile
      else if request.line > 0 then
        runLocalProbe snapshot request
      else if request.operation ∈ ["term", "synth", "reduce"] then
        let directive := match request.operation with
          | "synth" => s!"#synth {request.input}"
          | "reduce" => s!"#reduce {request.input}"
          | _ => s!"#check {request.input}"
        let source := request.source ++ "\n" ++ directive ++ "\n"
        let probeSnapshot ← processor (Parser.mkInputContext source fileName)
        let response ← processSnapshot probeSnapshot request.version false
        let detail := "\n".intercalate (response.diagnostics.toList.map (·.text))
        pure {response with detail}
      else
        pure (probeFailure "this probe requires FILE:LINE context" request.version)
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
