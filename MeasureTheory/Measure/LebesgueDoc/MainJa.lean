import MeasureTheory.Measure.LebesgueDoc.Build

open MTI

def main (args : List String) : IO UInt32 := do
  runLebesgueDocForLocale "ja" "_out/ja" args
