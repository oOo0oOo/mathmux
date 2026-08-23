import Lean.Elab.Frontend
import Lean.Language.Lean

open Lean Lean.Elab

structure Request where
  op : String := "check"
  source : String
  staleSource : String := ""
  reuse : Bool := true
  version : Nat := 0
deriving FromJson

structure Response where
  ok : Bool
  errors : Nat := 0
  messages : Nat := 0
  version : Nat := 0
  reused : Bool := false
  detail : String := ""
deriving ToJson

def writeResponse (response : Response) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn (toJson response).compress
  stdout.flush

unsafe def loadFixture : IO Environment := do
  enableInitializersExecution
  importModules #[{module := `MathmuxFixture.Shared}] {} 0 (loadExts := true)

def responseOfMessages (messages : MessageLog) (version : Nat) (reused : Bool) : Response :=
  let messages := messages.toList
  let errors := messages.countP fun message => message.severity == .error
  {ok := errors == 0, errors, messages := messages.length, version, reused}

def processIncremental (env : Environment) (source : String)
    (old? : Option IncrementalState := none) : BaseIO IncrementalState := do
  let inputCtx := Parser.mkInputContext source "<mathmux>"
  IO.processCommandsIncrementally inputCtx {} (Command.mkState env {} {}) old?

partial def finalCommandState (snap : Language.Lean.CommandParsedSnapshot) : Command.State :=
  match snap.nextCmdSnap? with
  | some next => finalCommandState next.get
  | none => snap.elabSnap.resultSnap.get.cmdState

def processLanguageCommands (env : Environment) (source : String)
    (old? : Option (Parser.InputContext × Language.Lean.CommandParsedSnapshot) := none) :
    BaseIO (Parser.InputContext × Language.Lean.CommandParsedSnapshot) := do
  let inputCtx := Parser.mkInputContext source "<mathmux>"
  let task ← Language.Lean.processCommands inputCtx {} (Command.mkState env {} {}) old?
  return (inputCtx, task.get)

def setupImports (stx : HeaderSyntax) :
    Language.ProcessingT IO
      (Except Language.Lean.HeaderProcessedSnapshot Language.Lean.SetupImportsResult) := do
  let header := stx.toModuleHeader
  return .ok {
    mainModuleName := `MathmuxFixture.Worker
    isModule := header.isModule
    imports := header.imports
    opts := Elab.async.set {} true
  }

def mkFullProcessor : BaseIO (Parser.InputContext → BaseIO Language.Lean.InitialSnapshot) :=
  Language.mkIncrementalProcessor (Language.Lean.process setupImports)

def responseOfInitialSnapshot (snap : Language.Lean.InitialSnapshot)
    (version : Nat) (reused : Bool) : Response :=
  match Language.Lean.waitForFinalCmdState? snap with
  | none => {ok := false, errors := 1, version, reused, detail := "header processing failed"}
  | some state => responseOfMessages state.messages version reused

unsafe def runServer (mode : String) : IO Unit := do
  enableInitializersExecution
  let env? ← if mode == "full" then pure none else some <$> loadFixture
  let processor ← mkFullProcessor
  let incrementalRef : IO.Ref (Option IncrementalState) ← IO.mkRef none
  let commandsRef : IO.Ref (Option (Parser.InputContext × Language.Lean.CommandParsedSnapshot)) ←
    IO.mkRef none
  let used ← IO.mkRef false
  let stdin ← IO.getStdin
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return
    if line.trimAscii.isEmpty then loop else
    match Json.parse line >>= fromJson? with
    | .error error =>
      writeResponse {ok := false, errors := 1, detail := error}
      loop
    | .ok (request : Request) =>
      let reused ← used.get
      let response ← if request.op == "supersede" && mode == "full" then do
        let _ ← processor (Parser.mkInputContext request.staleSource "<mathmux-stale>")
        let snap ← processor (Parser.mkInputContext request.source "<mathmux-current>")
        pure (responseOfInitialSnapshot snap request.version true)
      else match mode with
      | "full" => do
        let snap ← processor (Parser.mkInputContext request.source "<mathmux>")
        pure (responseOfInitialSnapshot snap request.version reused)
      | "commands" => do
        let some env := env?
          | pure {ok := false, errors := 1, detail := "missing prepared environment"}
        let old? ← if request.reuse then commandsRef.get else pure none
        let result@(_, snap) ← processLanguageCommands env request.source old?
        commandsRef.set (some result)
        pure (responseOfMessages (finalCommandState snap).messages request.version old?.isSome)
      | "incremental" => do
        let some env := env?
          | pure {ok := false, errors := 1, detail := "missing prepared environment"}
        let old? ← if request.reuse then incrementalRef.get else pure none
        let state ← processIncremental env request.source old?
        incrementalRef.set (some state)
        pure (responseOfMessages state.commandState.messages request.version old?.isSome)
      | _ => pure {ok := false, errors := 1, detail := s!"unknown mode: {mode}"}
      used.set true
      writeResponse response
      loop
  loop

unsafe def regionSave (path : System.FilePath) : IO Unit := do
  let env ← loadFixture
  let _ ← CompactedRegion.save path `MathmuxPreparedEnvironment env #[] none true
  writeResponse {ok := true}

unsafe def regionCheck (path : System.FilePath) : IO Unit := do
  enableInitializersExecution
  let (env, _) ← CompactedRegion.read (α := Environment) path #[]
  let source ← (← IO.getStdin).readToEnd
  let state ← processIncremental env source
  writeResponse (responseOfMessages state.commandState.messages 1 false)

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["server", mode] => runServer mode; return 0
  | ["region-save", path] => regionSave path; return 0
  | ["region-check", path] => regionCheck path; return 0
  | _ =>
    IO.eprintln "usage: mathmuxBench server full|commands|incremental | region-save FILE | region-check FILE"
    return 2
