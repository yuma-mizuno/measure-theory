import DocGen.Support.Style
import Verso.Doc.Concrete.InlineString
import VersoManual

open Verso Genre Manual
open Verso.Doc Elab
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Genre.Manual.InlineLean.Scopes
open SubVerso.Highlighting
open Lean Elab

noncomputable section

block_extension anchoredDeclBlock (cfg : AnchoredDeclConfig) where
  data := ToJson.toJson cfg
  traverse _ _ _ _ := pure none
  toHtml := open Verso.Output.Html in
    some <| fun _goI goB _id data contents => do
      let declId :=
        match FromJson.fromJson? (α := AnchoredDeclConfig) data with
        | .ok cfg => cfg.tokenId
        | .error _ => ""
      pure {{
        <div class="mv-lean-decl" id={{declId}} data-decl-id={{declId}}>
          {{← contents.mapM goB}}
        </div>
      }}
  toTeX := open Verso.Output.TeX in
    some <| fun _goI goB _id _data contents => do
      contents.mapM goB
  preamble := []
  extraCss := [leanCodeCss]
  extraJs := [leanDeclAnchorJs]

block_extension leanCodeFoldBlock where
  traverse _ _ _ _ := pure none
  toHtml := open Verso.Output.Html in
    some <| fun _goI goB _id _data contents => do
      pure {{
        <details class="mv-lean-code">
          <summary>"Lean code"</summary>
          <div class="mv-lean-code-body">{{← contents.mapM goB}}</div>
        </details>
      }}
  toTeX := open Verso.Output.TeX in
    some <| fun _goI goB _id _data contents => do
      let body ← contents.mapM goB
      pure <| Verso.Output.TeX.seq #[
        Verso.Output.TeX.raw "\\par\\medskip\\noindent\\texttt{Lean code}\\par\\smallskip",
        body,
        Verso.Output.TeX.raw "\\par\\medskip"
      ]
  preamble := []
  extraCss := [leanCodeCss, languageSwitcherCss]
  extraJs := [languageSwitcherJs, leanDeclAnchorJs]

@[role]
def leanLink : RoleExpanderOf NameConfig
  | cfg, #[arg] => do
    let name ← Verso.Doc.oneCodeStr #[arg]
    let identStx := mkIdentFrom arg (cfg.full.getD name.getString.toName) (canonical := true)
    try
      let resolvedName ←
        runWithOpenDecls <| runWithVariables fun _ =>
          withInfoTreeContext
              (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo
                { elaborator := `DocGen.Support.LeanCode.leanLink, stx := identStx })) do
            realizeGlobalConstNoOverloadWithInfo identStx
      let hl : Highlighted ← constTok resolvedName name.getString
      let target ←
        `(Inline.other
            {Verso.Genre.Manual.InlineLean.Inline.name with data := ToJson.toJson $(quote hl)}
            #[Inline.code $(quote name.getString)])
      pure target
    catch e =>
      logErrorAt identStx e.toMessageData
      ``(Inline.code $(quote name.getString))
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"
