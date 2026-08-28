import Lean.Language.Lean
import Lean.Setup
import Lean.Server.InfoUtils
import Lean.Elab.Tactic
import Loogle.Find

open Lean Lean.Elab
open Lean.Core Lean.Meta Lean.Elab Lean.Elab.Term
open Loogle

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

def deduplicateDiagnostics (diagnostics : Array Diagnostic) : Array Diagnostic := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut unique := #[]
  for diagnostic in diagnostics do
    let key := diagnostic.severity ++ "\u0000" ++ diagnostic.kind ++ "\u0000" ++ diagnostic.text
    if !seen.contains key then
      seen := seen.insert key
      unique := unique.push diagnostic
  return unique

structure ProfileEntry where
  line : Nat
  column : Nat
  kind : String
  detail : String
  duration_ms : Float
deriving ToJson

structure TypeSearchHit where
  name : String
  type : String
  module : Option String := none
  doc : Option String := none
deriving ToJson

structure Response where
  ok : Bool
  diagnostics : Array Diagnostic
  profile : Array ProfileEntry := #[]
  detail : String := ""
  count : Nat := 0
  hits : Array TypeSearchHit := #[]
  suggestions : Array String := #[]
  version : Nat
deriving ToJson

def useGoalsAfter (goal : GoalsAtResult) : Bool :=
  goal.useAfter && !goal.tacticInfo.goalsAfter.isEmpty

def goalContext (goal : GoalsAtResult) : ContextInfo :=
  { goal.ctxInfo with
    mctx := if useGoalsAfter goal then goal.tacticInfo.mctxAfter else goal.tacticInfo.mctxBefore }

def goalMVars (goal : GoalsAtResult) : List MVarId :=
  if useGoalsAfter goal then goal.tacticInfo.goalsAfter else goal.tacticInfo.goalsBefore

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

def contextBetweenOffsets (trees : Array InfoTree) (start stop : Nat) : Option ContextInfo := Id.run do
  for tree in trees do
    for offset in [start:stop + 1] do
      if let some info := tree.termGoalAt? ⟨offset⟩ then
        return some info.ctx
  return none

partial def contextInSnapshotTree (tree : Language.SnapshotTree) (fileMap : FileMap)
    (start stop : Nat) : BaseIO (Option ContextInfo) := do
  if let some ctx := contextBetweenOffsets tree.element.infoTree?.toArray start stop then
    return some ctx
  for child in tree.children do
    if let some ctx ← contextInSnapshotTree child.get fileMap start stop then
      return some ctx
  return none

def contextAtPosition (tree : Language.SnapshotTree) (fileMap : FileMap)
    (line column : Nat) : BaseIO (Option ContextInfo) := do
  if line == 0 then return none
  let zeroLine := line - 1
  let start := fileMap.ofPosition {line := zeroLine, column := column - 1}
  if column > 0 then
    return ← contextInSnapshotTree tree fileMap start.byteIdx start.byteIdx
  let stop := fileMap.ofPosition {line := zeroLine + 1, column := 0}
  contextInSnapshotTree tree fileMap start.byteIdx stop.byteIdx

def parseCategory (category : Name) (source : String) : CoreM Syntax := do
  match Parser.runParserCategory (← getEnv) category source with
  | .ok stx => pure stx
  | .error error => throwError error

def throwLoggedErrors : Term.TermElabM Unit := do
  let messages ← Core.getMessageLog
  if messages.hasErrors then
    let mut details := #[]
    for message in messages.reportedPlusUnreported do
      if message.severity == .error then
        details := details.push (← message.toString)
    throwError ("\n".intercalate details.toList)

def inspectTerm (operation source : String) : Term.TermElabM String := do
  let stx ← parseCategory `term source
  if operation == "synth" then
    let type ← Term.elabType stx
    Term.synthesizeSyntheticMVarsNoPostponing
    throwLoggedErrors
    let type ← instantiateMVars type
    let value ← Meta.synthInstance type
    return s!"{(← Meta.ppExpr value).pretty} : {(← Meta.ppExpr type).pretty}"
  let value ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
  throwLoggedErrors
  let value ← instantiateMVars value
  if value.isSyntheticSorry then
    throwError "term elaboration failed"
  Meta.check value
  if operation == "reduce" then
    return (← Meta.ppExpr (← Meta.reduce value)).pretty
  return s!"{(← Meta.ppExpr value).pretty} : {(← Meta.ppExpr (← Meta.inferType value)).pretty}"

def evalTacticText (source : String) : Tactic.TacticM Unit := do
  let stx ← parseCategory `term s!"by {source}"
  match stx with
  | `(term| by $tactics:tacticSeq) => Tactic.evalTactic tactics
  | _ => throwError "invalid tactic sequence"

def probeFailure (detail : String) (version : Nat) : Response :=
  { ok := false,
    diagnostics := #[{ severity := "error", kind := "mathmux", text := detail }],
    detail,
    version }

def runLocalProbe (snapshot : Language.Lean.InitialSnapshot) (request : Request) : IO Response := do
  let tree := Language.toSnapshotTree snapshot
  let fileMap := snapshot.ictx.fileMap
  let goal? ← goalAtPosition tree fileMap request.line request.column
  try
    let detail ← if request.operation == "goal" then
      let some goal := goal?
        | throw <| IO.userError s!"no tactic context at line {request.line}"
      let mvars := goalMVars goal
      let ctx := goalContext goal
      pure (← ctx.ppGoals mvars).pretty
    else if request.operation == "tactic" then
      let some goal := goal?
        | throw <| IO.userError s!"no tactic context at line {request.line}"
      let mvars := goalMVars goal
      let ctx := goalContext goal
      ctx.runMetaM {} do
        let action : Tactic.TacticM String := do
          evalTacticText request.input
          let remaining ← Tactic.getUnsolvedGoals
          if remaining.isEmpty then return "solved"
          let formats ← liftM (m := MetaM) (remaining.mapM Meta.ppGoal)
          return (Std.Format.prefixJoin "\n" formats).pretty
        (((action {elaborator := .anonymous}).run' {goals := mvars}) {}).run' {}
    else
      match goal? with
      | some goal =>
        let some mvar := (goalMVars goal).head?
          | throw <| IO.userError "probe position has no active goal"
        (goalContext goal).runMetaM {} do
          mvar.withContext do
            (inspectTerm request.operation request.input {}).run' {}
      | none =>
        let some ctx ← contextAtPosition tree fileMap request.line request.column
          | throw <| IO.userError s!"no elaboration context at line {request.line}"
        ctx.runMetaM {} do
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
  let diagnostics := deduplicateDiagnostics (← renderMessages messages)
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
      let response ← if request.operation ∉ ["check", "goal", "tactic", "term", "synth", "reduce"] then
        pure (probeFailure s!"unknown file operation: {request.operation}" request.version)
      else if request.operation == "check" then
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

def parseTypeSearchQuery (env : Environment) (input : String) : Except String Syntax :=
  let parser := Parser.andthenFn Parser.whitespace (Parser.evalParserConst `Loogle.Find.find_filters)
  let context := Parser.mkInputContext input "<mathmux-type-search>"
  let state := parser.run context { env, options := {} } (Parser.getTokenTable env)
    (Parser.mkParserState input)
  if state.hasError then
    .error (state.toErrorMsg context)
  else if state.pos.atEnd input then
    .ok state.stxStack.back
  else
    .error ((state.mkError "end of input").toErrorMsg context)

open PrettyPrinter in
def typeSearchSignature (name : Name) : MetaM String := withCurrHeartbeats do
  let expression ← mkConstWithLevelParams name
  let (stx, _) ← delabCore expression (delab := Delaborator.delabConstWithSignature)
  let stx : Syntax := stx
  return (← ppTerm ⟨stx[1]!⟩).pretty (width := 10000)

abbrev TypeSearchQueryResult := Except String Find.Result × Array String

def runTypeSearchQuery (index : Find.Index) (request : Request) : CoreM Response :=
    withCurrHeartbeats do
  let (result, suggestions) : TypeSearchQueryResult ← tryCatchRuntimeEx
    (handler := fun error => do
      return (.error (← error.toMessageData.toString), #[])) do
      match parseTypeSearchQuery (← getEnv) request.input with
      | .error error => pure (.error error, #[])
      | .ok stx => MetaM.run' do
        match ← TermElabM.run' <| Find.find index (.mk stx) (maxShown := 24) with
        | .ok result =>
          let suggestions ← result.suggestions.mapM fun suggestion => do
            return (← PrettyPrinter.ppCategory ``Find.find_filters suggestion).pretty
              (width := 10000)
          pure (.ok result, suggestions)
        | .error error =>
          let suggestions ← error.suggestions.mapM fun suggestion => do
            return (← PrettyPrinter.ppCategory ``Find.find_filters suggestion).pretty
              (width := 10000)
          pure (.error (← error.message.toString), suggestions)
  match result with
  | .error error =>
    return {
      ok := false
      diagnostics := #[]
      detail := error
      suggestions
      version := request.version
    }
  | .ok result =>
    let detail ← result.header.toString
    let hits ← result.hits.take 24 |>.mapM fun (info, module?) => do
      let type ← (typeSearchSignature info.name).run'
      let doc ← findDocString? (← getEnv) info.name false
      return {
        name := info.name.toString
        type
        module := module?.map (·.toString)
        doc
      }
    return {
      ok := true
      diagnostics := #[]
      detail
      count := result.count
      hits
      suggestions
      version := request.version
    }

unsafe def runTypeSearchServer (module : Name) (indexPath : System.FilePath) : IO Unit := do
  enableInitializersExecution
  let serverStarted ← IO.monoMsNow
  let environment ← importModules (loadExts := true)
    #[{module}, {module := `Loogle.Find}] {}
  let environmentReady ← IO.monoMsNow
  let context := { fileName := "/", fileMap := Inhabited.default }
  let state := { env := environment }
  let action : CoreM Unit := do
    let cached ← indexPath.pathExists
    let indexStarted ← IO.monoMsNow
    let index ← if cached then
      let (cache, _) ← unpickle _ indexPath
      Find.Index.mkFromCache cache
    else
      Find.Index.mk
    let indexReady ← IO.monoMsNow
    let started ← IO.monoMsNow
    let nameRelFinished ← IO.mkRef started
    let trieFinished ← IO.mkRef started
    let recordNameRelFinished : MetaM Unit := do nameRelFinished.set (← IO.monoMsNow)
    let recordTrieFinished : MetaM Unit := do trieFinished.set (← IO.monoMsNow)
    (index.1.cache.startInBackground recordNameRelFinished).run'
    (index.2.cache.startInBackground recordTrieFinished).run'
    let _ ← index.1.cache.get.run'
    let _ ← index.2.cache.get.run'
    let pickleStarted ← IO.monoMsNow
    unless cached do
      pickle indexPath (← index.getCache)
    let finished ← IO.monoMsNow
    let profile := #[
      {line := 0, column := 0, kind := "type-search-import", detail := "", duration_ms := (environmentReady - serverStarted).toFloat},
      {line := 0, column := 0, kind := "type-search-index-open", detail := "", duration_ms := (indexReady - indexStarted).toFloat},
      {line := 0, column := 0, kind := "type-search-name-relation", detail := "", duration_ms := ((← nameRelFinished.get) - started).toFloat},
      {line := 0, column := 0, kind := "type-search-name-trie", detail := "", duration_ms := ((← trieFinished.get) - started).toFloat},
      {line := 0, column := 0, kind := "type-search-index-pickle", detail := "", duration_ms := (finished - pickleStarted).toFloat}
    ]
    writeResponse {ok := true, diagnostics := #[], profile, detail := "ready", version := 0}
    let stdin ← IO.getStdin
    while true do
      let line ← stdin.getLine
      if line.isEmpty then break
      if !line.trimAscii.isEmpty then
        let response ← match Json.parse line >>= fromJson? with
          | .error error => pure (failureResponse error 0)
          | .ok (request : Request) =>
            if request.operation == "type_search" then
              runTypeSearchQuery index request
            else
              pure (probeFailure s!"unknown type-search operation: {request.operation}" request.version)
        writeResponse response
  let (_, _) ← action.toIO context state

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["file", setupPath] => runServer (← ModuleSetup.load setupPath) false; return 0
  | ["file", setupPath, "--profile"] => runServer (← ModuleSetup.load setupPath) true; return 0
  | ["type-search", module, indexPath] => runTypeSearchServer module.toName indexPath; return 0
  | _ =>
    IO.eprintln "usage: MathmuxLeanService (file SETUP_JSON [--profile] | type-search MODULE INDEX)"
    return 2
