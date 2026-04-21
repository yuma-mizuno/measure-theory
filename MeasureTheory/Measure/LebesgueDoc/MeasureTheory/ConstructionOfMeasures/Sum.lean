import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Measures.Sum"
lebesgue_doc_module MeasureTheory.Lean.Measures.Sum
open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Sum" =>

%%%
file := "Sum"
tag := "sum"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "測度の総和")
:::

:::::definitionBox
::::localized
Let $`X` be a measurable space, let $`I` be an index set,
and let $`\mu_i` for $`i \in I` be a family of measures on $`X`.
Their _sum_ is the measure defined by
$$`
  \left(\sum_{i \in I} \mu_i\right)(A) \coloneqq \sum_{i \in I} \mu_i(A)
`
for any measurable set $`A \subseteq X`.
:::locale "ja"
$`X` を可測空間とし、$`I` を添字集合、$`\mu_i` (for $`i \in I`) を $`X` 上の測度族とする。
それらの _総和_ を、任意の可測集合 $`A \subseteq X` に対して
$$`
  \left(\sum_{i \in I} \mu_i\right)(A) \coloneqq \sum_{i \in I} \mu_i(A)
`
で定まる測度として定義する。
:::
::::
:::::

```leanDecl
MTI.Measure.sum
MTI.Measure.sum_apply
```

:::::lemmaBox
::::localized
The lower integral commutes with the sum:
$$`
  \underline{\int}_{x \in X} f(x)\,d\left(\sum_{i \in I} \mu_i\right)
    =
  \sum_{i \in I} \underline{\int}_{x \in X} f(x)\,d\mu_i.
`
:::locale "ja"
下積分は総和と交換する:
$$`
  \underline{\int}_{x \in X} f(x)\,d\left(\sum_{i \in I} \mu_i\right)
    =
  \sum_{i \in I} \underline{\int}_{x \in X} f(x)\,d\mu_i.
`
:::
::::
:::::

```leanDecl
MTI.lintegral_sum_measure
```
