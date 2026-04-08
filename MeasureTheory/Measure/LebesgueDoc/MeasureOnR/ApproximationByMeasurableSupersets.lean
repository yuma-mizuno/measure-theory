import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lebesgue.MeasurableCaratheodory"
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.MeasurableCaratheodory

open Verso Genre Manual

#doc (Manual) "Approximation by Measurable Supersets" =>

%%%
file := "Approximation-by-Measurable-Supersets"
tag := "approximation-by-measurable-supersets"
%%%

:::localizedPart (ja := "可測上位集合による近似")
:::

:::lebesgueDocSetup
:::

:::::theoremBox
::::localized
For any set
$`A \subseteq \mathbb{R}`,
$$`m(A) =
\inf_{\substack{B \subseteq \mathbb{R} \\ \text{$B$ is measurable},\, A \subseteq B}} m(B).`
:::locale "ja"
任意の集合
$`A \subseteq \mathbb{R}` に対して
$$`
  m(A) =
  \inf_{\substack{B \subseteq \mathbb{R} \\ \text{$B$ is measurable},\, A \subseteq B}} m(B).
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_eq_iInf
```

:::::theoremBox
::::localized
For any set $`A \subseteq \mathbb{R}`,
there exists a measurable set $`B \subseteq \mathbb{R}` such that
$`A \subseteq B` and $`m(B) = m(A).`
:::locale "ja"
任意の集合 $`A \subseteq \mathbb{R}` に対して、
$`A \subseteq B` かつ $`m(B) = m(A)` を満たす可測集合 $`B \subseteq \mathbb{R}` が存在する。
:::
::::
:::::

```leanDecl
MTI.Real.exists_measurable_superset_measure_eq
```
