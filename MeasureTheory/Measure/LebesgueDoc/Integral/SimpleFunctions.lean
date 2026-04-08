import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.SimpleFunc"
lebesgue_doc_module MeasureTheory.Lean.SimpleFunc

open Verso Genre Manual
open Verso.Genre.Manual.InlineLean

set_option maxHeartbeats 2000000 in
#doc (Manual) "Simple Functions" =>

%%%
file := "Simple-Functions"
tag := "simple-functions"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "単関数")
:::

:::::definitionBox
::::localized
Let $`X` be a measurable space.
A function $`f : X \to [0,\infty]` is called _simple_ if

1. for any $`a \in [0,\infty]`, the fiber $`f^{-1}\{a\}` is measurable, and
2. the image $`\operatorname{Im}f` is finite.
:::locale "ja"
$`X` を可測空間とする。
関数 $`f : X \to [0,\infty]` が _単関数_ であるとは、次を満たすことをいう。

1. 任意の $`a \in [0,\infty]` に対して、ファイバー $`f^{-1}\{a\}` が可測である。
2. 像 $`\operatorname{Im}f` が有限である。
:::
::::
:::::

```leanDecl
MTI.SimpleFunc
```

:::::definitionBox
::::localized
Let $`f : X \to [0,\infty]` be a simple function, and let $`\mu` be a measure on $`X`.
Its _integral_ is defined by
$$`
  \Simp \int_{x \in X} f(x)\,d\mu
    \coloneqq
  \sum_{y \in \operatorname{Im} f} y \cdot \mu(f^{-1}\{y\}).`
:::locale "ja"
$`f : X \to [0,\infty]` を単関数、$`\mu` を $`X` 上の測度とする。
その _積分_ を
$$`
  \Simp \int_{x \in X} f(x)\,d\mu
    \coloneqq
  \sum_{y \in \operatorname{Im} f} y \cdot \mu(f^{-1}\{y\})
`
で定める。
:::
::::
:::::

```leanDecl
MTI.SimpleFunc.lintegral
```
