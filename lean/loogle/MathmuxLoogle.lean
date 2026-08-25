/-
Derived from Loogle by Joachim Breitner.
Released under Apache 2.0; see LICENSE in this directory.
-/
import Lean.Meta
import Loogle.Find

set_option autoImplicit false

open Lean Core Meta Elab Term
open Loogle

namespace MathmuxLoogle

def Parser.run (env : Environment) (input : String) : Except String Syntax :=
  let parser := Parser.andthenFn Parser.whitespace (Parser.evalParserConst `Loogle.Find.find_filters)
  let context := Parser.mkInputContext input "<mathmux-search>"
  let state := parser.run context { env, options := {} } (Parser.getTokenTable env)
    (Parser.mkParserState input)
  if state.hasError then
    .error (state.toErrorMsg context)
  else if state.pos.atEnd input then
    .ok state.stxStack.back
  else
    .error ((state.mkError "end of input").toErrorMsg context)

open PrettyPrinter in
def signature (name : Name) : MetaM String := withCurrHeartbeats do
  let expression ← mkConstWithLevelParams name
  let (stx, _) ← delabCore expression (delab := Delaborator.delabConstWithSignature)
  let stx : Syntax := stx
  return (← ppTerm ⟨stx[1]!⟩).pretty (width := 10000)

abbrev QueryResult := Except String Find.Result × Array String

def query (index : Find.Index) (input : String) : CoreM Json := withCurrHeartbeats do
  let (result, suggestions) : QueryResult ← tryCatchRuntimeEx
    (handler := fun error => do
      return (.error (← error.toMessageData.toString), #[])) do
      match Parser.run (← getEnv) input with
      | .error error => pure (.error error, #[])
      | .ok stx => MetaM.run' do
        match ← TermElabM.run' <| Find.find index (.mk stx) with
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
    return .mkObj [
      ("error", .str error),
      ("suggestions", .arr (suggestions.map .str))
    ]
  | .ok result =>
    let hits ← result.hits.take 24 |>.mapM fun (info, module?) => do
      let type ← (signature info.name).run'
      let doc := match ← findDocString? (← getEnv) info.name false with
        | some value => .str value
        | none => .null
      let module := match module? with
        | some value => .str value.toString
        | none => .null
      return .mkObj [
        ("name", .str info.name.toString),
        ("type", .str type),
        ("module", module),
        ("doc", doc)
      ]
    return .mkObj [
      ("count", .num result.count),
      ("hits", .arr hits),
      ("suggestions", .arr (suggestions.map .str))
    ]

unsafe def run (module : Name) (indexPath : System.FilePath) : IO Unit := do
  enableInitializersExecution
  let environment ← importModules (loadExts := true)
    #[{module := module}, {module := `Loogle.Find}] {}
  let context := { fileName := "/", fileMap := Inhabited.default }
  let state := { env := environment }
  let action : CoreM Unit := do
    let index ← if ← indexPath.pathExists then
      let (cache, _) ← unpickle _ indexPath
      Find.Index.mkFromCache cache
    else
      Find.Index.mk
    let _ ← index.1.cache.get.run'
    let _ ← index.2.cache.get.run'
    unless ← indexPath.pathExists do
      pickle indexPath (← index.getCache)
    IO.println "Mathmux Loogle is ready."
    (← IO.getStdout).flush
    while true do
      let input := (← (← IO.getStdin).getLine).trimAscii.copy
      if input.isEmpty then break
      IO.println (← query index input).compress
      (← IO.getStdout).flush
  let (_, _) ← action.toIO context state

end MathmuxLoogle

unsafe def main (arguments : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match arguments with
  | [module, indexPath] => MathmuxLoogle.run module.toName indexPath; return 0
  | _ => IO.eprintln "usage: MathmuxLoogle MODULE INDEX"; return 2
