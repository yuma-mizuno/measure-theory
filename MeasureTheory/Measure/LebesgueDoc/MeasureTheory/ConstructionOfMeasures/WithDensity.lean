import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Measures.WithDensity"
lebesgue_doc_module MeasureTheory.Lean.Measures.WithDensity
open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "With Density" =>

%%%
file := "With-Density"
tag := "with-density"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "密度付き測度")
:::

:::::definitionBox
::::localized
Let $`X` be a measurable space, let $`\mu` be a measure on $`X`,
and let $`f : X \to [0,\infty]`.
We define a measure $`f \cdot \mu` by
$$`
  (f \cdot \mu)(A)
    \coloneqq
  \underline{\int}_{x \in A} f(x)\,d\mu
`
for any measurable set $`A \subseteq X`.
:::locale "ja"
$`X` を可測空間とし、$`\mu` を $`X` 上の測度、$`f : X \to [0,\infty]` を関数とする。
測度 $`f \cdot \mu` を、任意の可測集合 $`A \subseteq X` に対して
$$`
  (f \cdot \mu)(A)
    \coloneqq
  \underline{\int}_{x \in A} f(x)\,d\mu
`
で定める。
:::
::::
:::::

```leanDecl
MTI.Measure.withDensity
MTI.Measure.withDensity_apply
```

:::::lemmaBox
::::localized
Let $`f, g : X \to [0,\infty]` be measurable.
Then
$$`
  \underline{\int}_{x \in X} g(x)\,d(f \cdot \mu)
    =
  \underline{\int}_{x \in X} f(x) g(x)\,d\mu.
`
:::locale "ja"
$`f, g : X \to [0,\infty]` を可測とする。
このとき
$$`
  \underline{\int}_{x \in X} g(x)\,d(f \cdot \mu)
    =
  \underline{\int}_{x \in X} f(x) g(x)\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.lintegral_withDensity_eq_lintegral_mul
```
