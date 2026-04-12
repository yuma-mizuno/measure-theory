import Lean.Util.Path

namespace MTI

def defaultLegacyManifestPath : System.FilePath := "scripts/legacy-paths.txt"

private def mirrorManifestName : System.FilePath := ".root-doc-manifest"

private def removePathIfPresent (path : System.FilePath) : IO Unit := do
  if ← path.pathExists then
    if ← path.isDir then
      IO.FS.removeDirAll path
    else
      IO.FS.removeFile path

private def cleanMirror (dest : System.FilePath) : IO Unit := do
  let manifestPath := dest / mirrorManifestName
  if ← manifestPath.pathExists then
    let manifest ← IO.FS.readFile manifestPath
    for relPath in manifest.splitOn "\n" do
      if !relPath.isEmpty then
        removePathIfPresent (dest / relPath)
    IO.FS.removeFile manifestPath

partial def copyRecursively (src dest : System.FilePath) : IO Unit := do
  if ← src.isDir then
    IO.FS.createDirAll dest
    for entry in ← src.readDir do
      copyRecursively entry.path (dest / entry.fileName)
  else
    dest.parent.forM IO.FS.createDirAll
    IO.FS.writeBinFile dest (← IO.FS.readBinFile src)

private def mirrorTree (src dest : System.FilePath) : IO Unit := do
  unless ← src.pathExists do
    throw <| IO.userError s!"Expected generated documentation at '{src}'"
  cleanMirror dest
  let entries ← src.readDir
  for entry in entries do
    copyRecursively entry.path (dest / entry.fileName)
  let manifest := String.intercalate "\n" <| entries.toList.map (·.fileName)
  IO.FS.writeFile (dest / mirrorManifestName) manifest

private def appendComponents (base : System.FilePath) (comps : List String) : System.FilePath :=
  base / System.mkFilePath comps

private def parentComponents? (path : System.FilePath) : Option (List String) :=
  match path.components.reverse with
  | "index.html" :: rest => some rest.reverse
  | _ => none

private def targetComponents? (oldDir : List String) : Option (List String) :=
  match oldDir with
  | "html-multi" :: rel => some rel
  | "ja" :: "html-multi" :: rel => some ("ja" :: rel)
  | _ => none

private def redirectTargetUrl (oldDir targetDir : List String) : String :=
  let up := String.intercalate "" <| List.replicate oldDir.length "../"
  let down :=
    if targetDir.isEmpty then
      ""
    else
      String.intercalate "/" targetDir ++ "/"
  up ++ down

private def redirectHtml (target : String) : String := String.intercalate "\n"
  [ "<!DOCTYPE html>"
  , "<html lang=\"en\">"
  , "<head>"
  , "  <meta charset=\"utf-8\">"
  , s!"  <meta http-equiv=\"refresh\" content=\"0; url={target}\">"
  , "  <meta name=\"robots\" content=\"noindex\">"
  , "  <title>Redirecting…</title>"
  , s!"  <link rel=\"canonical\" href=\"{target}\">"
  , "  <script>"
  , "    (function () {"
  , s!"      const target = new URL(\"{target}\", window.location.href);"
  , "      target.search = window.location.search;"
  , "      target.hash = window.location.hash;"
  , "      window.location.replace(target.href);"
  , "    })();"
  , "  </script>"
  , "</head>"
  , "<body>"
  , s!"  <p><a href=\"{target}\">Continue to the current page</a></p>"
  , "</body>"
  , "</html>"
  ]

private def writeRedirect (outputDir : System.FilePath) (oldRel target : String) : IO Unit := do
  let path := outputDir / oldRel
  path.parent.forM IO.FS.createDirAll
  IO.FS.writeFile path (redirectHtml target)

private def applyLegacyRedirects (outputDir legacyManifest : System.FilePath) : IO Unit := do
  unless ← legacyManifest.pathExists do
    throw <| IO.userError s!"Expected legacy redirect manifest at '{legacyManifest}'"
  let manifest ← IO.FS.readFile legacyManifest
  for line in manifest.splitOn "\n" do
    let oldRel := line.trimAscii.toString
    if oldRel.isEmpty || oldRel.startsWith "#" then
      continue
    let oldPath : System.FilePath := oldRel
    let some oldDir := parentComponents? oldPath
      | throw <| IO.userError s!"Unsupported legacy path in manifest: '{oldRel}'"
    let some targetDir := targetComponents? oldDir
      | throw <| IO.userError s!"Unsupported legacy path in manifest: '{oldRel}'"
    let targetIndex := appendComponents outputDir targetDir / "index.html"
    if ← targetIndex.pathExists then
      writeRedirect outputDir oldRel (redirectTargetUrl oldDir targetDir)
    else
      IO.eprintln s!"warning: skipping legacy redirect without current target: {oldRel}"

def postprocessPagesOutput (outputDir legacyManifest : System.FilePath) : IO Unit := do
  mirrorTree (outputDir / "html-multi") outputDir
  let jaHtmlMulti := outputDir / "ja" / "html-multi"
  if ← jaHtmlMulti.pathExists then
    mirrorTree jaHtmlMulti (outputDir / "ja")
  applyLegacyRedirects outputDir legacyManifest

end MTI
