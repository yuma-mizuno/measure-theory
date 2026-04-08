import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lebesgue.SimpleFunc"
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.SimpleFunc
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.Lintegral

open Verso Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Simple Functions on ℝ" =>

%%%
file := "Simple-Functions-on-R"
tag := "simple-functions-on-r"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "実数直線上の単関数")
:::

:::::definitionBox
::::localized
Let $`f : \mathbb{R} \to [0,\infty]`.
We call $`f` _simple_ if

1. for any $`a \in [0,\infty]`, the fiber $`f^{-1}\{a\}` is measurable, and
2. the image $`\operatorname{Im}f` is finite.
:::locale "ja"
$`f : \mathbb{R} \to [0,\infty]` とする。
$`f` が _単関数_ であるとは、次を満たすことをいう。

1. 任意の $`a \in [0,\infty]` に対して、ファイバー $`f^{-1}\{a\}` が可測である。
2. 像 $`\operatorname{Im}f` が有限である。
:::
::::
:::::

```leanDecl
MTI.Real.SimpleFunc
```

:::::definitionBox
::::localized
Let $`f : \mathbb{R} \to [0,\infty]` be simple.
Its _integral_ is defined by
$$`
  \Simp \int_{x \in \mathbb{R}} f(x)\,dx
    \coloneqq
  \sum_{y \in \operatorname{Im} f} y \cdot m(f^{-1}\{y\}).`
:::locale "ja"
$`f : \mathbb{R} \to [0,\infty]` を単関数とする。
その _積分_ を
$$`
  \Simp \int_{x \in \mathbb{R}} f(x)\,dx
    \coloneqq
  \sum_{y \in \operatorname{Im} f} y \cdot m(f^{-1}\{y\})
`
で定める。
:::
::::
:::::

```leanDecl
MTI.Real.SimpleFunc.lintegral
```
