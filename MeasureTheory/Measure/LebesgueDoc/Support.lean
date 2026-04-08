import DocGen.Support
import Mathlib.Tactic.Linter.Style
import Std.Data.HashMap
import Verso.Code.External
import Verso.Doc.ArgParse
import MeasureTheory.Measure.LebesgueDoc.Assets
import MeasureTheory.Measure.LebesgueDoc.Config
import MeasureTheory.Measure.LebesgueDoc.DeclStore

set_option verso.exampleProject "."

open Verso Genre Manual
open Verso.Doc Elab
open Verso.Code.External
open Lean Elab

noncomputable section

initialize registerTraceClass `MTI.LebesgueDoc.leanDecl

private def externalCodeConfig : CodeConfig :=
  { showProofStates := true, defSite := some false }

private structure LeanDeclTargetConfig where
  requestedName : Name
  displayName : String
deriving ToJson, FromJson

private def displayNameOfDeclName (declName : Name) : String :=
  match declName.toString.splitOn "." |>.reverse with
  | last :: _ => last
  | [] => declName.toString

block_extension lebesgueLeanDeclTargetBlock (cfg : LeanDeclTargetConfig) via withHighlighting where
  data := ToJson.toJson cfg
  traverse id data _ := do
    match FromJson.fromJson? data with
    | .error err =>
        logError s!"Failed to deserialize leanDecl target config during traversal: {err}"
        pure none
    | .ok (cfg : LeanDeclTargetConfig) =>
        saveExampleDefs id #[(cfg.requestedName, cfg.displayName)]
        pure none
  toHtml := open Verso.Output.Html in
    some <| fun _goI _goB _id _data _contents => pure .empty
  toTeX := open Verso.Output.TeX in
    some <| fun _goI _goB _id _data _contents => pure .empty
  preamble := []

private structure LeanDeclProfile where
  moduleLoadMs : Nat := 0
  declLookupMs : Nat := 0
  blockBuildMs : Nat := 0
deriving Inhabited

private abbrev LeanDeclProfileRef := IO.Ref LeanDeclProfile

private initialize lebesgueItemCache :
    IO.Ref (Std.HashMap (Name × Name) SubVerso.Module.ModuleItem) ←
  IO.mkRef {}

private def timeIfProfiling {α : Type} (profileRef? : Option LeanDeclProfileRef) (x : DocElabM α) :
    DocElabM (Nat × α) := do
  match profileRef? with
  | none =>
      return (0, ← x)
  | some _ =>
      let start ← IO.monoMsNow
      let result ← x
      let stop ← IO.monoMsNow
      return (stop - start, result)

private def modifyProfile (profileRef? : Option LeanDeclProfileRef)
    (f : LeanDeclProfile → LeanDeclProfile) : IO Unit := do
  match profileRef? with
  | none => pure ()
  | some profileRef => profileRef.modify f

private def getProfile (profileRef? : Option LeanDeclProfileRef) : IO LeanDeclProfile := do
  match profileRef? with
  | none => pure {}
  | some profileRef => profileRef.get

private def withLookupProfiling
    {α : Type} (profileRef? : Option LeanDeclProfileRef) (x : DocElabM α) :
    DocElabM α := do
  let startLoadMs := (← getProfile profileRef?).moduleLoadMs
  let (elapsedMs, result) ← timeIfProfiling profileRef? x
  let endLoadMs := (← getProfile profileRef?).moduleLoadMs
  modifyProfile profileRef? fun profile =>
    { profile with declLookupMs := profile.declLookupMs + (elapsedMs - (endLoadMs - startLoadMs)) }
  return result

private def cacheItem (moduleName declName : Name) (item : SubVerso.Module.ModuleItem) : IO Unit :=
  lebesgueItemCache.modify fun cache =>
    cache.insert (moduleName.eraseMacroScopes, declName.eraseMacroScopes) item

private def ensureDocDeclStore (profileRef? : Option LeanDeclProfileRef) (moduleName : Name) :
    DocElabM Unit := do
  let (loadMs, _) ←
    timeIfProfiling profileRef? <| MTI.LebesgueDoc.ensureDeclStore moduleName
  modifyProfile profileRef? fun profile =>
    { profile with moduleLoadMs := profile.moduleLoadMs + loadMs }
  if loadMs > 0 then
    trace[MTI.LebesgueDoc.leanDecl]
      "module {moduleName}: ensure decl store {loadMs}ms"

private def findCachedDocItem? (moduleName declName : Name) :
    DocElabM (Option SubVerso.Module.ModuleItem) := do
  let key := (moduleName.eraseMacroScopes, declName.eraseMacroScopes)
  return (← lebesgueItemCache.get)[key]?

private def loadDocItemInModule? (moduleName declName : Name) :
    DocElabM (Option SubVerso.Module.ModuleItem) := do
  let declName := declName.eraseMacroScopes
  if let some item ← findCachedDocItem? moduleName declName then
    return some item
  if let some item ← MTI.LebesgueDoc.loadDeclArtifact moduleName declName then
    cacheItem moduleName declName item
    return some item
  return none

private def resolveDocCandidates
    (requestedName : Name)
    (candidates : Array MTI.LebesgueDoc.DocDecl) :
    DocElabM SubVerso.Module.ModuleItem := do
  let mut hits := #[]
  for candidate in candidates do
    if let some item ← loadDocItemInModule? candidate.moduleName candidate.lookupName then
      hits := hits.push (candidate, item)
  if hits.isEmpty then
    if candidates.size == 1 then
      let some candidate := candidates[0]?
        | throwError m!"Internal error while resolving {requestedName}"
      throwError
        m!"Declaration {requestedName} was not found in the highlighted module \
            for {candidate.moduleName}"
    throwError
      m!"{requestedName} was not found. Add `lebesgue_doc_module` for its source module."
  if hits.size = 1 then
    let some (candidate, item) := hits[0]?
      | throwError m!"Internal error while resolving {requestedName}"
    if requestedName != candidate.lookupName then
      cacheItem candidate.moduleName requestedName item
    return item
  let moduleList :=
    String.intercalate ", " <| hits.toList.map fun (candidate, _) => toString candidate.moduleName
  throwError
    m!"Declaration {requestedName} is ambiguous across registered source modules: {moduleList}. \
        Use `lebesgue_doc_alias` to choose one explicitly."

private def findDocItem (profileRef? : Option LeanDeclProfileRef) (declName : Name) :
    DocElabM SubVerso.Module.ModuleItem := do
  let declName := declName.eraseMacroScopes
  let env ← getEnv
  let pageModule ← getMainModule
  let sourceState := MTI.LebesgueDoc.docSourceState env pageModule
  let candidates :=
    match sourceState.aliases[declName]? with
    | some docDecl => #[docDecl]
    | none => sourceState.modules.map fun moduleName => { moduleName, lookupName := declName }
  for candidate in candidates do
    ensureDocDeclStore profileRef? candidate.moduleName
  withLookupProfiling profileRef? do
    resolveDocCandidates declName candidates

private def tokenIdOfDeclName (declName : Name) : String :=
  String.intercalate "___" (declName.toString.splitOn ".")

private def warnOnCommandOnlyLeanDeclTarget (declName : Name) : DocElabM Unit := do
  let declName := declName.eraseMacroScopes
  let env ← getEnv
  if env.isConstructor declName then
    let parentMsg :=
      match env.find? declName with
      | some (.ctorInfo info) => m!" It is generated by `{info.induct}`."
      | _ => m!""
    logWarning
      m!"`leanDecl {declName}` targets a constructor.{parentMsg} Current Verso rendering is \
          command-level, so this block will render the containing command rather than a focused \
          declaration snippet."
  else if env.isProjectionFn declName then
    logWarning
      m!"`leanDecl {declName}` targets a projection. Current Verso rendering is command-level, \
          so this block will render the containing structure/class command rather than a focused \
          declaration snippet."

-- Large declarations can require substantial elaboration while Verso expands code blocks.
set_option maxHeartbeats 2000000 in
@[code_block_expander leanDecl]
def leanDecl : CodeBlockExpander
  | args, code => do
    ArgParse.done.run args
    let declNames :=
      code.getString.splitOn "\n"
        |>.map (fun s => s.trimAscii.copy)
        |>.filter (not ∘ String.isEmpty)
    if declNames.isEmpty then
      throwErrorAt code "Expected at least one declaration name"
    let profiling := (← isTracingEnabledFor `MTI.LebesgueDoc.leanDecl)
    let profileRef? ← if profiling then some <$> IO.mkRef {} else pure none
    let pageModule ← getMainModule
    let (totalMs, blocks) ← timeIfProfiling profileRef? do
      let mut blocks := #[]
      for declNameStr in declNames do
        let declName := declNameStr.toName
        warnOnCommandOnlyLeanDeclTarget declName
        let beforeProfile ← getProfile profileRef?
        let item ← findDocItem profileRef? declName
        let afterLookupProfile ← getProfile profileRef?
        let (blockBuildMs, wrapped) ← timeIfProfiling profileRef? do
          let targetBlock ← ``(
            Verso.Doc.Block.other
              (lebesgueLeanDeclTargetBlock
                (LeanDeclTargetConfig.mk
                  $(quote declName.eraseMacroScopes)
                  $(quote <| displayNameOfDeclName declName)))
              #[])
          let codeBlock ← ``(Verso.Code.External.ExternalCode.leanBlock
            (genre := Manual)
            $(quote item.code)
            $(quote externalCodeConfig))
          ``(
            Verso.Doc.Block.other
              (anchoredDeclBlock (AnchoredDeclConfig.mk $(quote <| tokenIdOfDeclName declName)))
              #[$targetBlock, $codeBlock])
        modifyProfile profileRef? fun profile =>
          { profile with blockBuildMs := profile.blockBuildMs + blockBuildMs }
        let afterProfile ← getProfile profileRef?
        trace[MTI.LebesgueDoc.leanDecl]
          "decl {declName}: module load \
            {(afterLookupProfile.moduleLoadMs - beforeProfile.moduleLoadMs)}ms, \
            decl lookup {(afterLookupProfile.declLookupMs - beforeProfile.declLookupMs)}ms, \
            block build {(afterProfile.blockBuildMs - afterLookupProfile.blockBuildMs)}ms"
        blocks := blocks.push wrapped
      pure blocks
    let profile ← getProfile profileRef?
    let accountedMs := profile.moduleLoadMs + profile.declLookupMs + profile.blockBuildMs
    trace[MTI.LebesgueDoc.leanDecl]
      "leanDecl in {pageModule}: {declNames.length} declarations, \
        module load {profile.moduleLoadMs}ms, decl lookup {profile.declLookupMs}ms, \
        block build {profile.blockBuildMs}ms, other {totalMs - accountedMs}ms, \
        total {totalMs}ms"
    pure #[← ``(Verso.Doc.Block.other leanCodeFoldBlock #[$[$blocks],*])]

end
