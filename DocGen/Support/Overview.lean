import DocGen.Support.Common

open Verso Genre Manual
open Verso.Doc Elab
open Lean Elab

noncomputable section

block_extension chapterOverviewBlock where
  traverse _ _ _ _ := pure none
  toHtml := open Verso.Output.Html in
    some <| fun _ _ _ _ _ => do
      let locale ← getOutputLocaleHtml
      let title := if locale == "ja" then "この章のまとめ" else "Chapter Overview"
      let headerLevel := (← read).traverseContext.headers.size + 2
      pure <| Verso.Output.Html.tag s!"h{headerLevel}" #[] title
  toTeX := open Verso.Output.TeX in
    some <| fun _ _ _ _ _ => do
      let locale ← getOutputLocaleTeX
      let title : Verso.Output.TeX := .text <|
        if locale == "ja" then "この章のまとめ" else "Chapter Overview"
      let (_, ctxt, _, _) ← read
      let level := ctxt.headers.size + 1
      Verso.Doc.TeX.headerLevel title level none
  preamble := []

@[block_command]
def chapterOverview : BlockCommandOf Unit
  | () => ``(Block.other chapterOverviewBlock #[])
