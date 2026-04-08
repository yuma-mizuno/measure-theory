import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Measures.Pushforward"
lebesgue_doc_module MeasureTheory.Lean.Measures.Pushforward
open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Pushforward" =>

%%%
file := "Pushforward"
tag := "pushforward"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "押し出し測度")
:::

::::localized
Pushforward is the operation that transports a measure along a measurable map.
:::locale "ja"
押し出しは、可測写像に沿って測度を運ぶ操作です。
:::
::::

:::::definitionBox
::::localized
Let $`X` and $`Y` be measurable spaces, let $`\mu` be a measure on $`X`,
and let $`f : X \to Y` be measurable.
The _pushforward_ of $`\mu` along $`f`, denoted by $`f_*\mu`,
is the measure on $`Y` defined by
$$`
  (f_*\mu)(A) \coloneqq \mu(f^{-1}(A))
`
for measurable sets $`A \subseteq Y`.
:::locale "ja"
$`X` と $`Y` を可測空間とし、$`\mu` を $`X` 上の測度、$`f : X \to Y` を可測写像とする。
$`f` に沿った $`\mu` の _押し出し_ とは、$`Y` の任意の可測集合 $`A \subseteq Y` に対して
$$`
  (f_*\mu)(A) \coloneqq \mu(f^{-1}(A))
`
で定まる $`Y` 上の測度 $`f_*\mu` のことである。
:::
::::
:::::

```leanDecl
MTI.Measure.map
MTI.Measure.map_apply
```

:::::lemmaBox
::::localized
Let $`g : Y \to [0,\infty]` be measurable.
Then
$$`
  \underline{\int}_{y \in Y} g(y)\,d(f_*\mu)
    =
  \underline{\int}_{x \in X} g(f(x))\,d\mu.
`
:::locale "ja"
$`g : Y \to [0,\infty]` を可測とする。
このとき
$$`
  \underline{\int}_{y \in Y} g(y)\,d(f_*\mu)
    =
  \underline{\int}_{x \in X} g(f(x))\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.lintegral_map
```
