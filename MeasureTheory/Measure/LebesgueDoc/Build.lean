import VersoManual
import DocGen.Support
import MeasureTheory.Measure.LebesgueDoc

open Verso Doc
open Verso.Genre Manual

namespace MTI

def lebesgueDocConfig : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def localizedLebesgueDoc (locale : String) : Part Manual :=
  applyLocalizationToPart locale <| %doc MeasureTheory.Measure.LebesgueDoc

private def cleanGeneratedOutput (dest : System.FilePath) : IO Unit := do
  for dir in [dest / "html-multi", dest / "html-single", dest / "tex"] do
    if ← dir.pathExists then
      IO.FS.removeDirAll dir

def runLebesgueDocForLocale (locale : String) (dest : System.FilePath) (args : List String) :
    IO UInt32 := do
  setOutputLocale locale
  cleanGeneratedOutput dest
  manualMain (localizedLebesgueDoc locale)
    (options := args) (config := { lebesgueDocConfig with destination := dest })

def extractOutputDir (args : List String) :
    Except String (Option System.FilePath × List String) := Id.run do
  let rec go (output? : Option System.FilePath) (kept : List String) : List String →
      Except String (Option System.FilePath × List String)
    | [] => .ok (output?, kept.reverse)
    | "--output" :: dir :: rest => go (some dir) kept rest
    | ["--output"] => .error "Missing directory after --output"
    | arg :: rest => go output? (arg :: kept) rest
  go none [] args

end MTI
