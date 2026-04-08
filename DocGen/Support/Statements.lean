import DocGen.Support.Style

open Verso Genre Manual
open Verso.Doc Elab
open Lean Elab

noncomputable section

structure StatementKind where
  name : String
  jaName : String
  classSuffix : String
  italic : Bool
  background : String
  borderColor : String
  accentStart : String
  accentEnd : String
deriving Inhabited, ToJson, FromJson

open Syntax in
instance : Quote StatementKind where
  quote kind := mkCApp ``StatementKind.mk #[
    quote kind.name,
    quote kind.jaName,
    quote kind.classSuffix,
    quote kind.italic,
    quote kind.background,
    quote kind.borderColor,
    quote kind.accentStart,
    quote kind.accentEnd
  ]

private def theoremKind : StatementKind :=
  {
    name := "Theorem"
    jaName := "定理"
    classSuffix := "theorem"
    italic := true
    background := "rgba(255, 255, 255, 0.84)"
    borderColor := "var(--mv-line)"
    accentStart := "var(--mv-accent)"
    accentEnd := "#ff8b7a"
  }

private def lemmaKind : StatementKind :=
  {
    name := "Lemma"
    jaName := "補題"
    classSuffix := "lemma"
    italic := true
    background := "rgba(255, 255, 255, 0.84)"
    borderColor := "var(--mv-line)"
    accentStart := "var(--mv-accent-2)"
    accentEnd := "#ffd166"
  }

private def definitionKind : StatementKind :=
  {
    name := "Definition"
    jaName := "定義"
    classSuffix := "definition"
    italic := false
    background := "rgba(255, 248, 240, 0.92)"
    borderColor := "rgba(217, 173, 102, 0.24)"
    accentStart := "var(--mv-accent-2)"
    accentEnd := "#f0b38a"
  }

private def statementConfigOfJson (data : Json) : StatementBoxConfig :=
  match FromJson.fromJson? data with
  | .ok cfg => cfg
  | .error _ => {}

private def localizedTitle (locale : String) (title? ja? : Option String) : Option String :=
  if locale == "ja" then ja? <|> title? else title?

private def localizedStatementKind (kind : StatementKind) (locale : String) : String :=
  if locale == "ja" then kind.jaName else kind.name

private def statementHeading
    (kind : StatementKind) (locale : String) (title? ja? : Option String) : String :=
  let kind := localizedStatementKind kind locale
  let title? := localizedTitle locale title? ja?
  match title? with
  | some title => s!"{kind} ({title})."
  | none => s!"{kind}."

private def statementTeX (kind : StatementKind) (locale : String) (title? ja? : Option String)
    (label : Verso.Output.TeX) (body : Verso.Output.TeX) : Verso.Output.TeX :=
  let kindName := localizedStatementKind kind locale
  let title? := localizedTitle locale title? ja?
  let titleTex : Verso.Output.TeX :=
    match title? with
    | some title =>
        Verso.Output.TeX.seq #[
          Verso.Output.TeX.raw ("\\par\\medskip\\noindent\\textbf{" ++ kindName ++ " ("),
          Verso.Output.TeX.text title,
          Verso.Output.TeX.raw <| ").} " ++ if kind.italic then "\\itshape " else ""
        ]
    | none =>
        Verso.Output.TeX.raw <|
          "\\par\\medskip\\noindent\\textbf{" ++ kindName ++ ".} " ++
          if kind.italic then "\\itshape " else ""
  Verso.Output.TeX.seq #[
    titleTex,
    label,
    body,
    Verso.Output.TeX.raw "\\par\\medskip"
  ]

private def statementTitleForXref (kind : StatementKind) (cfg : StatementBoxConfig) : String :=
  match cfg.title? with
  | some title => s!"{kind.name} ({title})"
  | none => kind.name

private def statementLabelTeX (id : InternalId) :
    Verso.Doc.TeX.TeXT Manual (ReaderT ExtensionImpls IO) Verso.Output.TeX := do
  let xref : TraverseState ←
    Verso.Doc.TeX.state (g := Manual) (m := ReaderT ExtensionImpls IO)
  pure <|
    match xref.externalTags[id]? with
    | some (link : Multi.Link) =>
        Verso.Output.TeX.raw <|
          "\\label{" ++ Verso.Output.TeX.labelForTeX link.htmlId ++ "}"
    | none => .empty

private def registerStatementTag
    {m : Type → Type}
    [Monad m] [MonadState TraverseState m] [MonadLiftT IO m] [MonadReaderOf TraverseContext m]
    (kind : StatementKind) (id : InternalId) (cfg : StatementBoxConfig) : m Unit := do
  let some tag := cfg.tag? | return ()
  let requestedSlug := tag.sluggify
  if (← get).externalTags.toArray.any fun (otherId, link) =>
      otherId != id && link.htmlId == requestedSlug then
    logError s!"Duplicate tag '{tag}'"
    return
  let path := (← read).path
  let _ ← externalTag id path tag
  let some link := (← get).externalTags[id]? | return ()
  let context := (← read).headers
  let jsonMetadata :=
    Json.arr <| context.map fun (h : PartHeader) => json%{
      "title": $h.titleString,
      "shortTitle": $(h.metadata.bind (·.shortTitle)),
      "number": $(h.metadata.bind (·.assignedNumber) |>.map toString)
    }
  let sectionNum := sectionString (← read)
  let title := statementTitleForXref kind cfg
  modify fun st =>
    st.saveDomainObject sectionDomain link.htmlId.toString id
      |>.saveDomainObjectData sectionDomain link.htmlId.toString (json%{
        "context": $jsonMetadata,
        "title": $title,
        "shortTitle": $(cfg.title?),
        "sectionNum": $sectionNum
      })

private def statementVariantClass (kind : StatementKind) : String :=
  "mv-" ++ kind.classSuffix

private def statementStyleVars (kind : StatementKind) : String :=
  String.intercalate " " [
    s!"--mv-statement-bg: {kind.background};",
    s!"--mv-statement-border: {kind.borderColor};",
    s!"--mv-statement-accent-start: {kind.accentStart};",
    s!"--mv-statement-accent-end: {kind.accentEnd};"
  ]

block_extension statementBlock (kind : StatementKind) (cfg : StatementBoxConfig) where
  data := ToJson.toJson (kind, cfg)
  traverse id data _ := do
    let (kind, cfg) :
        StatementKind × StatementBoxConfig :=
      match FromJson.fromJson? data with
      | .ok pair => pair
      | .error _ => (default, {})
    registerStatementTag kind id cfg
    pure none
  toHtml := open Verso.Output.Html in
    some <| fun _goI goB id data contents => do
      let (kind, cfg) :
          StatementKind × StatementBoxConfig :=
        match FromJson.fromJson? data with
        | .ok pair => pair
        | .error _ => (default, {})
      let locale ← getOutputLocaleHtml
      let xref ← Verso.Doc.Html.HtmlT.state
      let attrs := xref.htmlId id
      let heading := statementHeading kind locale cfg.title? cfg.ja?
      let variantClass := statementVariantClass kind
      pure {{
        <div class={{"mv-statement " ++ variantClass}} style={{statementStyleVars kind}} {{attrs}}>
          {{permalink id xref false}}
          <div class="mv-statement-title">{{ heading }}</div>
          <div class="mv-statement-body">{{← contents.mapM goB}}</div>
        </div>
      }}
  toTeX := open Verso.Output.TeX in
    some <| fun _goI goB id data contents => do
      let (kind, cfg) :
          StatementKind × StatementBoxConfig :=
        match FromJson.fromJson? data with
        | .ok pair => pair
        | .error _ => (default, {})
      let locale ← getOutputLocaleTeX
      pure <|
        statementTeX kind locale cfg.title? cfg.ja?
          (← statementLabelTeX id) (← contents.mapM goB)
  preamble := []
  extraCss := [statementBlockCss, languageSwitcherCss]
  extraJs := [languageSwitcherJs]

@[directive]
def theoremBox : DirectiveExpanderOf StatementBoxConfig
  | cfg, contents => do
    ``(Verso.Doc.Block.other
      (statementBlock $(quote theoremKind) $(quote cfg))
      #[$[$(← contents.mapM elabBlock)],*])

@[directive]
def lemmaBox : DirectiveExpanderOf StatementBoxConfig
  | cfg, contents => do
    ``(Verso.Doc.Block.other
      (statementBlock $(quote lemmaKind) $(quote cfg))
      #[$[$(← contents.mapM elabBlock)],*])

@[directive]
def definitionBox : DirectiveExpanderOf StatementBoxConfig
  | cfg, contents => do
    ``(Verso.Doc.Block.other
      (statementBlock $(quote definitionKind) $(quote cfg))
      #[$[$(← contents.mapM elabBlock)],*])
