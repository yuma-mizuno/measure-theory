import Verso.Doc.ArgParse
import Verso.Doc.Elab
import Verso.Doc.Elab.Monad
import VersoManual.Basic

open Verso Genre Manual
open Verso.Doc Elab

namespace MTI

def theoremCss := r#"
.mv-theorem {
  margin: 1rem 0 1.25rem 0;
  padding: 0.9rem 1rem 0.75rem 1rem;
  border: 1px solid #98B2C0;
  border-left: 0.35rem solid #98B2C0;
  background: linear-gradient(180deg, #f8fbfc 0%, #ffffff 100%);
}

.mv-theorem-title {
  margin: 0 0 0.45rem 0;
  color: #1f3442;
  font-family: "STIX Two Text", "Times New Roman", serif;
  font-size: 1.05rem;
  font-style: normal;
  font-weight: 700;
  letter-spacing: 0.01em;
}

.mv-theorem-body {
  font-style: italic;
}

.mv-theorem-body > :first-child {
  margin-top: 0;
}

.mv-theorem-body > :last-child {
  margin-bottom: 0;
}
"#

block_extension Block.theorem where
  traverse _ _ _ _ := pure none
  toHtml := open Verso.Output.Html in
    some <| fun _goI goB _id _data contents => do
      pure {{
        <div class="mv-theorem">
          <div class="mv-theorem-title">"Theorem."</div>
          <div class="mv-theorem-body">{{← contents.mapM goB}}</div>
        </div>
      }}
  toTeX := open Verso.Output.TeX in
    some <| fun _goI goB _id _data contents => do
      pure \TeX{
        \begin{mvtheorem}
        \Lean{← contents.mapM goB}
        \end{mvtheorem}
      }
  preamble := [
    "\\newenvironment{mvtheorem}{\\par\\medskip\\noindent\\textbf{Theorem. }\\itshape}" ++
      "{\\par\\medskip}"
  ]
  extraCss := [theoremCss]

def theoremBoxImpl : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.theorem #[$[$(← contents.mapM elabBlock)],*])

end MTI

@[directive]
def theoremBox : DirectiveExpanderOf Unit
  | (), contents => MTI.theoremBoxImpl () contents
