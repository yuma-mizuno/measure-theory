import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Measures.Addition"
lebesgue_doc_module MeasureTheory.Lean.Measures.Addition
open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Addition" =>

%%%
file := "Addition"
tag := "addition"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "測度の和")
:::

:::::definitionBox
::::localized
Let $`X` be a measurable space, and let $`\mu` and $`\nu` be measures on $`X`.
Their _sum_ is the measure on $`X` defined by
$$`
  (\mu + \nu)(A) \coloneqq \mu(A) + \nu(A)
`
for any measurable set $`A \subseteq X`.
:::locale "ja"
$`X` を可測空間とし、$`\mu` と $`\nu` を $`X` 上の測度とする。
それらの _和_ とは、任意の可測集合 $`A \subseteq X` に対して
$$`
  (\mu + \nu)(A) \coloneqq \mu(A) + \nu(A)
`
で定まる $`X` 上の測度である。
:::
::::
:::::

```leanDecl
MTI.Measure.add
MTI.Measure.add_apply
```

:::::lemmaBox
::::localized
Lower integrals are additive with respect to the sum of measures:
$$`
  \underline{\int}_{x \in X} f(x)\,d(\mu + \nu)
    =
  \underline{\int}_{x \in X} f(x)\,d\mu
  +
  \underline{\int}_{x \in X} f(x)\,d\nu.
`
:::locale "ja"
下積分は測度の和に関して加法的である:
$$`
  \underline{\int}_{x \in X} f(x)\,d(\mu + \nu)
    =
  \underline{\int}_{x \in X} f(x)\,d\mu
  +
  \underline{\int}_{x \in X} f(x)\,d\nu.
`
:::
::::
:::::

```leanDecl
MTI.lintegral_add_measure
```
