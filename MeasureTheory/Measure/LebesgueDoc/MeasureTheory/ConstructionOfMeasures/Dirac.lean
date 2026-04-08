import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Measures.Bind"
lebesgue_doc_module MeasureTheory.Lean.Measures.Bind
open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Dirac" =>

%%%
file := "Dirac"
tag := "dirac-measures"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "ディラック測度")
:::

:::::definitionBox
::::localized
Let $`X` be a measurable space and let $`x \in X`.
The _Dirac measure_ $`\delta_x` is the measure on $`X` defined by
$$`
  \delta_x(A) \coloneqq 1_A(x)`
for measurable sets $`A \subseteq X`.
:::locale "ja"
$`X` を可測空間とし、$`x \in X` とする。
_ディラック測度_ $`\delta_x` とは、任意の可測集合 $`A \subseteq X` に対して
$$`
  \delta_x(A) \coloneqq 1_A(x)
`
で定まる $`X` 上の測度である。
:::
::::
:::::

```leanDecl
MTI.Measure.dirac
MTI.Measure.dirac_apply
```

:::::lemmaBox
::::localized
Let $`f : X \to [0,\infty]` be measurable.
Then
$$`
  \underline{\int}_{y \in X} f(y)\,d\delta_x = f(x).`
:::locale "ja"
$`f : X \to [0,\infty]` を可測とする。
このとき
$$`
  \underline{\int}_{y \in X} f(y)\,d\delta_x = f(x).
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Measure.dirac_lintegral
```
