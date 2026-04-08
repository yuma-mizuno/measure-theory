import MeasureTheory.Measure.LebesgueDoc.Build

open MTI

def main (args : List String) : IO UInt32 := do
  let (baseDest?, forwardedArgs) ←
    match extractOutputDir args with
    | .ok result => pure result
    | .error err => throw <| IO.userError err
  let baseDest := baseDest?.getD "_out"
  let enStatus ← runLebesgueDocForLocale "en" baseDest forwardedArgs
  let jaStatus ← runLebesgueDocForLocale "ja" (baseDest / "ja") forwardedArgs
  writeRootRedirect baseDest
  if enStatus == 0 && jaStatus == 0 then
    pure 0
  else
    pure 1
