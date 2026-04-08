#!/usr/bin/env node

import fs from "node:fs/promises";
import path from "node:path";
import { pathToFileURL } from "node:url";

const repoRoot = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..");
const katexModulePath = path.join(
  repoRoot,
  ".lake",
  "packages",
  "verso",
  "vendored-js",
  "katex",
  "katex.mjs"
);
const macrosPath = path.join(
  repoRoot,
  "MeasureTheory",
  "Measure",
  "LebesgueDoc",
  "katex-macros.json"
);
const defaultRoots = [
  path.join(repoRoot, "MeasureTheory", "Measure", "LebesgueDoc")
];

const { default: katex } = await import(pathToFileURL(katexModulePath).href);
const macros = JSON.parse(await fs.readFile(macrosPath, "utf8"));

function lineAndColumn(source, index) {
  let line = 1;
  let column = 1;
  for (let i = 0; i < index; i++) {
    if (source[i] === "\n") {
      line += 1;
      column = 1;
    } else {
      column += 1;
    }
  }
  return { line, column };
}

function extractMathSpans(source) {
  const spans = [];
  const pattern = /(\$\$?)`([\s\S]*?)`/g;
  for (const match of source.matchAll(pattern)) {
    const [, opener, expr] = match;
    spans.push({
      expr,
      displayMode: opener === "$$",
      start: match.index ?? 0
    });
  }
  return spans;
}

async function collectLeanFiles(root) {
  const entries = await fs.readdir(root, { withFileTypes: true });
  const nested = await Promise.all(entries.map(async (entry) => {
    const entryPath = path.join(root, entry.name);
    if (entry.isDirectory()) {
      return collectLeanFiles(entryPath);
    }
    return entry.isFile() && entry.name.endsWith(".lean") ? [entryPath] : [];
  }));
  return nested.flat();
}

function checkExpr(expr, displayMode) {
  katex.renderToString(expr, {
    throwOnError: true,
    displayMode,
    macros
  });
}

const roots = process.argv.slice(2);
const scanRoots =
  roots.length > 0 ? roots.map((p) => path.resolve(repoRoot, p)) : defaultRoots;

const leanFiles = (
  await Promise.all(scanRoots.map((root) => collectLeanFiles(root)))
).flat().sort();

const failures = [];

for (const file of leanFiles) {
  const source = await fs.readFile(file, "utf8");
  for (const span of extractMathSpans(source)) {
    try {
      checkExpr(span.expr, span.displayMode);
    } catch (error) {
      const { line, column } = lineAndColumn(source, span.start);
      failures.push({
        file: path.relative(repoRoot, file),
        line,
        column,
        expr: span.expr,
        message: error instanceof Error ? error.message : String(error)
      });
    }
  }
}

if (failures.length > 0) {
  console.error("KaTeX validation failed:");
  for (const failure of failures) {
    console.error(
      `${failure.file}:${failure.line}:${failure.column}: ${failure.message}`
    );
    console.error(`  math: ${failure.expr.replace(/\s+/g, " ").trim()}`);
  }
  process.exit(1);
}

console.log(`KaTeX validation passed for ${leanFiles.length} Lean files.`);
