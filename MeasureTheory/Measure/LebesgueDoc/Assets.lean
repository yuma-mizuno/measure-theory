import DocGen.Support

open Verso Genre Manual
open Verso.Doc Elab

noncomputable section

def lebesgueKatexMacroJson : String :=
  include_str "katex-macros.json"

def lebesgueKatexMacroJs : String :=
  String.intercalate "\n" [
    "(function () {",
    "  if (!window.katex || window.__mvLebesgueKatexMacrosPatched) return;",
    s!"  const extraMacros = {lebesgueKatexMacroJson};",
    "",
    "  const withMacros = (options) => {",
    "    const opts = options || {};",
    "    const macros = Object.assign({}, extraMacros, opts.macros || {});",
    "    return Object.assign({}, opts, { macros });",
    "  };",
    "",
    "  const render = window.katex.render.bind(window.katex);",
    "  window.katex.render = function (expr, elem, options) {",
    "    return render(expr, elem, withMacros(options));",
    "  };",
    "",
    "  if (typeof window.katex.renderToString === \"function\") {",
    "    const renderToString = window.katex.renderToString.bind(window.katex);",
    "    window.katex.renderToString = function (expr, options) {",
    "      return renderToString(expr, withMacros(options));",
    "    };",
    "  }",
    "",
    "  window.__mvLebesgueKatexMacrosPatched = true;",
    "})();"
  ]

def lebesgueTemporaryCss : String :=
  String.intercalate "\n" [
    "/* Temporarily hide the locale switcher until we restore it. */",
    "[aria-label=\"Language switcher\"] {",
    "  display: none !important;",
    "}"
  ]

def japaneseEmphasisCss : String :=
  String.intercalate "\n" [
    ".mv-locale-ja {",
    "  display: contents;",
    "}",
    "",
    ".mv-locale-ja em {",
    "  font-style: normal;",
    "  font-weight: 700;",
    "}"
  ]

block_extension lebesgueDocSetupBlock where
  traverse _ _ _ _ := pure none
  toHtml := some <| fun _goI _goB _id _data _contents => pure .empty
  toTeX := some <| fun _goI _goB _id _data _contents => pure .empty
  preamble := []
  extraCss := [pageThemeCss, lebesgueTemporaryCss, japaneseEmphasisCss]
  extraJs := [lebesgueKatexMacroJs]

@[directive]
def lebesgueDocSetup : DirectiveExpanderOf Unit
  | (), _ => ``(Verso.Doc.Block.other lebesgueDocSetupBlock #[])
