import DocGen.Support
import Std.Data.HashMap
import Verso.Code.External
import SubVerso.Module
import Lean.Util.Path

open Verso.Doc Elab
open Verso.Code.External
open Lean Elab

noncomputable section

namespace MTI.LebesgueDoc

private def docModuleRoot : StrLit := Syntax.mkStrLit "."

private def declStoreRoot : System.FilePath :=
  ".lake" / "build" / "lebesgue_doc" / "decls"

private initialize ensuredDeclStores : IO.Ref (Std.HashMap Name String) ←
  IO.mkRef {}

private def appendNamePath (base : System.FilePath) (name : Name) : System.FilePath :=
  base / System.mkFilePath (name.toString.splitOn ".")

private def highlightedJsonPath (moduleName : Name) : System.FilePath :=
  (appendNamePath (".lake" / "build" / "highlighted") moduleName).addExtension "json"

private def highlightedHashPath (moduleName : Name) : System.FilePath :=
  (appendNamePath (".lake" / "build" / "highlighted") moduleName).addExtension "json.hash"

private def moduleStoreDir (moduleName : Name) : System.FilePath :=
  appendNamePath declStoreRoot moduleName

private def moduleHashStoreDir (moduleName : Name) (sourceHash : String) : System.FilePath :=
  moduleStoreDir moduleName / sourceHash

private def declArtifactPath (moduleName : Name) (sourceHash : String) (declName : Name) :
    System.FilePath :=
  moduleHashStoreDir moduleName sourceHash /
    s!"{String.intercalate "___" (declName.toString.splitOn ".")}.json"

private def declArtifactCompletePath (moduleName : Name) (sourceHash : String) : System.FilePath :=
  moduleHashStoreDir moduleName sourceHash / ".complete"

private def parseJsonFile (path : System.FilePath) : DocElabM Json := do
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | .ok json => return json
  | .error err => throwError m!"Invalid JSON in {path}: {err}"

private def loadHighlightedModule (moduleName : Name) : DocElabM SubVerso.Module.Module := do
  let json ← parseJsonFile (highlightedJsonPath moduleName)
  match SubVerso.Module.Module.fromJson? json with
  | .ok mod => return mod
  | .error err =>
      throwError m!"Could not deserialize highlighted module for {moduleName}: {err}"

private def readSourceHash? (moduleName : Name) : IO (Option String) := do
  let path := highlightedHashPath moduleName
  if ← path.pathExists then
    return some ((← IO.FS.readFile path).trimAscii.copy)
  return none

private def modifiedTime? (path : System.FilePath) : IO (Option IO.FS.SystemTime) := do
  if ← path.pathExists then
    return some (← path.metadata).modified
  return none

private def findModuleOLean? (moduleName : Name) : IO (Option System.FilePath) := do
  try
    return some (← Lean.findOLean moduleName)
  catch _ =>
    return none

private def needsRefreshAgainst? (targetPath : System.FilePath) (referencePath : System.FilePath) :
    IO Bool := do
  match ← modifiedTime? targetPath, ← modifiedTime? referencePath with
  | some targetTime, some referenceTime => pure (targetTime < referenceTime)
  | none, some _ => pure true
  | _, none => pure false

private def ensureHighlightedModule (moduleName : Name) : DocElabM Unit := do
  let jsonPath := highlightedJsonPath moduleName
  let hashPath := highlightedHashPath moduleName
  let mut rebuild := !(← jsonPath.pathExists) || !(← hashPath.pathExists)
  if !rebuild then
    if let some oleanPath ← findModuleOLean? moduleName then
      rebuild := (← needsRefreshAgainst? jsonPath oleanPath) || (← needsRefreshAgainst? hashPath oleanPath)
  if !rebuild then
    return ()
  let _ ← loadModuleContent docModuleRoot moduleName.toString
  pure ()

private def writeDeclArtifacts (moduleName : Name) (sourceHash : String) : DocElabM Unit := do
  let mod ← loadHighlightedModule moduleName
  let storeDir := moduleHashStoreDir moduleName sourceHash
  IO.FS.createDirAll storeDir
  for item in mod.items do
    for declName in item.defines do
      IO.FS.writeFile (declArtifactPath moduleName sourceHash declName) (toJson item).compress
  IO.FS.writeFile (declArtifactCompletePath moduleName sourceHash) ""

def ensureDeclStore (moduleName : Name) : DocElabM String := do
  ensureHighlightedModule moduleName
  let some sourceHash ← readSourceHash? moduleName
    | throwError m!"Missing highlighted hash for {moduleName}"
  let completePath := declArtifactCompletePath moduleName sourceHash
  let mut rewrite := !(← completePath.pathExists)
  if !rewrite then
    let jsonPath := highlightedJsonPath moduleName
    let hashPath := highlightedHashPath moduleName
    rewrite := (← needsRefreshAgainst? completePath jsonPath) || (← needsRefreshAgainst? completePath hashPath)
  if rewrite then
    writeDeclArtifacts moduleName sourceHash
  ensuredDeclStores.modify fun cache => cache.insert moduleName sourceHash
  return sourceHash

def loadDeclArtifact (moduleName declName : Name) :
    DocElabM (Option SubVerso.Module.ModuleItem) := do
  let sourceHash ← ensureDeclStore moduleName
  let artifactPath := declArtifactPath moduleName sourceHash declName.eraseMacroScopes
  if !(← artifactPath.pathExists) then
    return none
  let json ← parseJsonFile artifactPath
  match SubVerso.Module.ModuleItem.fromJson? json with
  | .ok item => return some item
  | .error err =>
      throwError m!"Could not deserialize declaration artifact {artifactPath}: {err}"

end MTI.LebesgueDoc
