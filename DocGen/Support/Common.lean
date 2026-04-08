import Verso.Doc.ArgParse
import Verso.Doc.Concrete.InlineString
import Verso.Doc.Elab
import Verso.Doc.Elab.Monad
import Verso.Parser
import VersoManual

open Verso Genre Manual
open Verso.ArgParse
open Verso.Doc Elab
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Genre.Manual.InlineLean.Scopes
open Verso.Multi (AllRemotes)
open SubVerso.Highlighting
open Lean Elab
open Lean.Doc.Syntax

noncomputable section

structure StatementBoxConfig where
  title? : Option String := none
  ja? : Option String := none
  tag? : Option String := none
deriving ToJson, FromJson

open Syntax in
instance : Quote StatementBoxConfig where
  quote cfg := mkCApp ``StatementBoxConfig.mk #[quote cfg.title?, quote cfg.ja?, quote cfg.tag?]

instance : FromArgs StatementBoxConfig DocElabM where
  fromArgs :=
    (StatementBoxConfig.mk
      <$> ((some <$> ArgParse.positional' `title) <|> pure none)
      <*> (.named `ja .string true)
      <*> (.named `tag .string true))
    <* ArgParse.done

structure LocalizedPartConfig where
  ja? : Option String := none
  jaAuthor? : Option String := none
deriving ToJson, FromJson

open Syntax in
instance : Quote LocalizedPartConfig where
  quote cfg := mkCApp ``LocalizedPartConfig.mk #[quote cfg.ja?, quote cfg.jaAuthor?]

instance : FromArgs LocalizedPartConfig DocElabM where
  fromArgs :=
    (LocalizedPartConfig.mk
      <$> (.named `ja .string true)
      <*> (.named `jaAuthor .string true))
    <* ArgParse.done

structure IncludeBlocksConfig where
  name : Name

instance : FromArgs IncludeBlocksConfig DocElabM where
  fromArgs :=
    IncludeBlocksConfig.mk <$> .positional `name .resolvedName <* ArgParse.done

@[block_command]
def includeBlocks : BlockCommandOf IncludeBlocksConfig
  | { name } => do
    let ident := mkIdent name
    ``(($(ident) : Block Manual))

structure AnchoredDeclConfig where
  tokenId : String
deriving ToJson, FromJson

open Syntax in
instance : Quote AnchoredDeclConfig where
  quote cfg := mkCApp ``AnchoredDeclConfig.mk #[quote cfg.tokenId]

initialize outputLocaleRef : IO.Ref String ← IO.mkRef "en"

def setOutputLocale (locale : String) : IO Unit :=
  outputLocaleRef.set locale

private def getOutputLocaleIO : IO String := do
  outputLocaleRef.get

def getOutputLocaleTeX :
    Verso.Doc.TeX.TeXT Manual (ReaderT ExtensionImpls IO) String :=
  liftM (m := IO) <| getOutputLocaleIO

def getOutputLocaleHtml :
    Verso.Doc.Html.HtmlT Manual (ReaderT AllRemotes (ReaderT ExtensionImpls IO)) String := do
  let locale :
      ReaderT AllRemotes (ReaderT ExtensionImpls IO) String :=
    liftM (m := IO) <| getOutputLocaleIO
  liftM locale
