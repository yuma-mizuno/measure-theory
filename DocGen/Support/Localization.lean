import DocGen.Support.Style

open Verso Genre Manual
open Verso.Doc Elab
open Verso.Genre Manual
open Lean Elab
open Lean.Doc.Syntax

noncomputable section

private def localeWrapperClass (locale : String) : String :=
  s!"mv-locale-{locale}"

block_extension localizedPartBlock (cfg : LocalizedPartConfig) where
  data := ToJson.toJson cfg
  traverse _ _ _ _ := pure none
  toHtml := some <| fun _goI _goB _id _data _contents => pure .empty
  toTeX := some <| fun _goI _goB _id _data _contents => pure .empty
  preamble := []

@[directive]
def localizedPart : DirectiveExpanderOf LocalizedPartConfig
  | cfg, _contents =>
    ``(Verso.Doc.Block.other (localizedPartBlock $(quote cfg)) #[])

block_extension localeVariantBlock (locale : String) where
  data := ToJson.toJson locale
  traverse _ _ _ _ := pure none
  toHtml := open Verso.Output.Html in
    some <| fun _goI goB _id data contents => do
    let expectedLocale : String :=
      match FromJson.fromJson? data with
      | .ok locale => locale
      | .error _ => ""
    let locale ← getOutputLocaleHtml
    if locale == expectedLocale then
      let rendered ← contents.mapM goB
      pure <| {{<div class=s!"{localeWrapperClass locale}">{{rendered}}</div>}}
    else
      pure .empty
  toTeX := some <| fun _goI goB _id data contents => do
    let expectedLocale : String :=
      match FromJson.fromJson? data with
      | .ok locale => locale
      | .error _ => ""
    let locale ← getOutputLocaleTeX
    if locale == expectedLocale then
      contents.mapM goB
    else
      pure .empty
  preamble := []
  extraCss := [languageSwitcherCss]
  extraJs := [languageSwitcherJs]

private def localeVariantData? (block : Block Manual) : Option String :=
  match block with
  | .other container _ =>
      if container.name == ``localeVariantBlock then
        match FromJson.fromJson? container.data with
        | .ok locale => some locale
        | .error _ => none
      else
        none
  | _ => none

private def localizedSelection (locale : String) (contents : Array (Block Manual)) :
    Array (Block Manual) :=
  let defaults := contents.filter (localeVariantData? · |>.isNone)
  let overrides := contents.filter (fun block => localeVariantData? block == some locale)
  if overrides.isEmpty then defaults else overrides

block_extension localizedBlock where
  traverse _ _ _ _ := pure none
  toHtml := open Verso.Output.Html in
    some <| fun _goI goB _id _data contents => do
    let locale ← getOutputLocaleHtml
    let rendered ← (localizedSelection locale contents).mapM goB
    pure <| {{<div class=s!"{localeWrapperClass locale}">{{rendered}}</div>}}
  toTeX := some <| fun _goI goB _id _data contents => do
    let locale ← getOutputLocaleTeX
    (localizedSelection locale contents).mapM goB
  preamble := []
  extraCss := [languageSwitcherCss]
  extraJs := [languageSwitcherJs]

@[directive]
def localized : DirectiveExpanderOf Unit
  | (), contents => do
    let mut blocks := #[]
    for block in contents do
      match block with
      | `(block| ::: locale $lang:str { $inner:block* } ) =>
          let innerBlocks ← inner.mapM elabBlock
          blocks := blocks.push (← ``(
            Verso.Doc.Block.other (localeVariantBlock $(quote lang.getString)) #[$[$innerBlocks],*]))
      | _ =>
          blocks := blocks.push (← elabBlock block)
    ``(Verso.Doc.Block.other localizedBlock #[$[$blocks],*])

private partial def localizedPartConfig? (block : Block Manual) : Option LocalizedPartConfig :=
  match block with
  | .other container _ =>
      if container.name == ``localizedPartBlock then
        match FromJson.fromJson? container.data with
        | .ok cfg => some cfg
        | .error _ => none
      else
        none
  | .concat blocks =>
      blocks.findSome? localizedPartConfig?
  | _ => none

private partial def stripLocalizedPartBlocks (block : Block Manual) : Option (Block Manual) :=
  match block with
  | .other container _ =>
      if container.name == ``localizedPartBlock then none else some block
  | .concat blocks =>
      let kept := blocks.filterMap stripLocalizedPartBlocks
      some <| .concat kept
  | _ => some block

private def localizePartMetadata
    (locale : String) (cfg? : Option LocalizedPartConfig) (titleString : String)
    (metadata? : Option Manual.PartMetadata) : Option Manual.PartMetadata :=
  let base : Manual.PartMetadata := metadata?.getD {}
  let base :=
    if base.file.isSome then
      base
    else
      { base with file := some titleString.sluggify.toString }
  if locale != "ja" then
    some base
  else
    match cfg?.bind (·.jaAuthor?) with
    | some jaAuthor => some { base with authors := [jaAuthor] }
    | none => some base

partial def applyLocalizationToPart (locale : String) (part : Part Manual) : Part Manual :=
  let cfg? := part.content.findSome? localizedPartConfig?
  let title? := if locale == "ja" then cfg?.bind (·.ja?) else none
  let title := title?.map (fun t => #[Inline.text t]) |>.getD part.title
  let titleString := title?.getD part.titleString
  let metadata := localizePartMetadata locale cfg? part.titleString part.metadata
  let content := part.content.filterMap stripLocalizedPartBlocks
  let subParts := part.subParts.map (applyLocalizationToPart locale)
  { part with title, titleString, metadata, content, subParts }
