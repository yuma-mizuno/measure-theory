import MeasureTheory.Lean.Lebesgue.MeasurableCaratheodory
import MeasureTheory.Lean.Lebesgue.MeasurableSets
import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lebesgue.MeasurableCaratheodory"
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.MeasurableCaratheodory
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.MeasurableSets

open Verso Genre Manual

#doc (Manual) "Measurable Sets Are Carathéodory" =>

%%%
file := "Measurable-Sets-Are-Caratheodory"
tag := "measurable-sets-are-caratheodory"
%%%

:::localizedPart (ja := "可測集合はカラテオドリ")
:::

:::lebesgueDocSetup
:::

:::::lemmaBox
::::localized
For any $`c \in \mathbb{R}`, the half-line $`[c,\infty)` is Carathéodory.
:::locale "ja"
任意の $`c \in \mathbb{R}` に対して、半直線 $`[c,\infty)` はカラテオドリである。
:::
::::
:::::

```leanDecl
MTI.Real.isCaratheodory_Ici
```

:::::theoremBox
::::localized
Any measurable set is Carathéodory.
:::locale "ja"
任意の可測集合はカラテオドリである。
:::
::::
:::::

```leanDecl
MTI.Real.MeasurableSet.isCaratheodory
```

:::::theoremBox
::::localized
Let $`A_1, A_2 \subseteq \mathbb{R}`. Suppose that $`A_1` and $`A_2` are disjoint and
that $`A_1` is measurable. Then
$`m(A_1 \cup A_2) = m(A_1) + m(A_2)`.
:::locale "ja"
$`A_1, A_2 \subseteq \mathbb{R}` とする。
$`A_1` と $`A_2` が交わらず、$`A_1` が可測であると仮定する。
このとき $`m(A_1 \cup A_2) = m(A_1) + m(A_2)` が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_union
```

:::::theoremBox "Continuity from below" (ja := "下からの連続性")
::::localized
Let $`A_0, A_1, \dots \subset \mathbb{R}` be a monotonically increasing sequence of measurable sets.
Then
$$`m(\bigcup_{n \in \mathbb{N}} A_n) = \sup_{n \in \mathbb{N}} m(A_n).`
:::locale "ja"
$`A_0, A_1, \dots \subset \mathbb{R}` を可測集合の単調増大列とする。
このとき
$$`
  m(\bigcup_{n \in \mathbb{N}} A_n) = \sup_{n \in \mathbb{N}} m(A_n).
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_iUnion_of_monotone
```

:::::theoremBox "Countable additivity" (ja := "可算加法性")
::::localized
Let $`A_0, A_1, \dots \subset \mathbb{R}` be a pairwise disjoint sequence of measurable sets. Then
$$`m(\bigcup_{n \in \mathbb{N}} A_n) = \sum_{n \in \mathbb{N}} m(A_n).`
:::locale "ja"
$`A_0, A_1, \dots \subset \mathbb{R}` を互いに交わらない可測集合の列とする。
このとき
$$`
  m(\bigcup_{n \in \mathbb{N}} A_n) = \sum_{n \in \mathbb{N}} m(A_n).
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_iUnion
```
