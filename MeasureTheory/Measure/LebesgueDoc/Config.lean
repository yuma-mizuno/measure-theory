import Lean
import Std.Data.HashMap

open Lean Elab Command

namespace MTI.LebesgueDoc

structure DocDecl where
  moduleName : Name
  lookupName : Name

structure DocSourceState where
  modules : Array Name := #[]
  aliases : Std.HashMap Name DocDecl := {}
deriving Inhabited

inductive DocSourceEntry where
  | module (pageModule : Name) (sourceModule : Name)
  | alias (pageModule : Name) (declName : Name) (target : DocDecl)

private def updateDocSourceState (cfg : DocSourceState) (entry : DocSourceEntry) : DocSourceState :=
  match entry with
  | .module _ sourceModule =>
      { cfg with modules := cfg.modules.push sourceModule }
  | .alias _ declName target =>
      { cfg with aliases := cfg.aliases.insert declName.eraseMacroScopes target }

private def updateDocSourceMap
    (states : Std.HashMap Name DocSourceState) (entry : DocSourceEntry) :
    Std.HashMap Name DocSourceState :=
  let pageModule :=
    match entry with
    | .module pageModule _ => pageModule
    | .alias pageModule _ _ => pageModule
  let cfg := states[pageModule]?.getD {}
  states.insert pageModule (updateDocSourceState cfg entry)

initialize docSourceExt :
    SimplePersistentEnvExtension DocSourceEntry (Std.HashMap Name DocSourceState) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun imported =>
      imported.foldl
        (init := {})
        fun acc entries =>
          entries.foldl updateDocSourceMap acc
    addEntryFn := updateDocSourceMap
  }

def docSourceState (env : Environment) (pageModule : Name) : DocSourceState :=
  (docSourceExt.getState env)[pageModule]?.getD {}

syntax (name := lebesgueDocModuleCmd) "lebesgue_doc_module " ident : command
syntax (name := lebesgueDocAliasCmd)
  "lebesgue_doc_alias " ident " from " ident " => " ident : command

@[command_elab lebesgueDocModuleCmd] def elabLebesgueDocModuleCmd : CommandElab
  | `(lebesgue_doc_module $moduleId:ident) => do
      let pageModule ← getMainModule
      modifyEnv fun env => docSourceExt.addEntry env (.module pageModule moduleId.getId)
  | _ => throwUnsupportedSyntax

@[command_elab lebesgueDocAliasCmd] def elabLebesgueDocAliasCmd : CommandElab
  | `(lebesgue_doc_alias $declId:ident from $moduleId:ident => $lookupId:ident) => do
      let pageModule ← getMainModule
      let target : DocDecl := { moduleName := moduleId.getId, lookupName := lookupId.getId }
      modifyEnv fun env => docSourceExt.addEntry env (.alias pageModule declId.getId target)
  | _ => throwUnsupportedSyntax

end MTI.LebesgueDoc
