import MeasureTheory.Measure.LebesgueDoc.Support

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lebesgue.Caratheodory"
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.Caratheodory
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.MeasurableCaratheodory

open Verso Genre Manual

#doc (Manual) "Carathéodory's Criterion" =>

%%%
file := "Caratheodorys-Criterion"
tag := "caratheodorys-criterion"
%%%

:::localizedPart (ja := "カラテオドリの判定条件")
:::

:::lebesgueDocSetup
:::

:::::definitionBox
::::localized
A set $`A \subseteq \mathbb{R}` is _Carathéodory_ if
for any set $`B \subseteq \mathbb{R}` one has
$`m(B) = m(B \cap A) + m(B \setminus A)`.
:::locale "ja"
集合 $`A \subseteq \mathbb{R}` が _カラテオドリ_ であるとは、任意の集合 $`B \subseteq \mathbb{R}` に対して
$`m(B) = m(B \cap A) + m(B \setminus A)` が成り立つことをいう。
:::
::::
:::::

```leanDecl
MTI.Real.IsCaratheodory
```

:::::lemmaBox
::::localized
Let $`A_1, A_2 \subseteq \mathbb{R}`. Suppose that $`A_1` and $`A_2` are disjoint and
that $`A_1` is Carathéodory. Then
$`m(A_1 \cup A_2) = m(A_1) + m(A_2)`.
:::locale "ja"
$`A_1, A_2 \subseteq \mathbb{R}` とする。
$`A_1` と $`A_2` が交わらず、$`A_1` がカラテオドリであると仮定する。
このとき $`m(A_1 \cup A_2) = m(A_1) + m(A_2)` が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_c_union
```

:::::lemmaBox
::::localized
Carathéodory sets are closed under union, complement, intersection.
:::locale "ja"
カラテオドリ集合の和集合、補集合、共通部分も再びカラテオドリである。
:::
::::
:::::

```leanDecl
MTI.Real.IsCaratheodory.union
MTI.Real.IsCaratheodory.compl
MTI.Real.IsCaratheodory.inter
```

:::::lemmaBox
::::localized
Countable unions of Carathéodory sets are again Carathéodory.
:::locale "ja"
カラテオドリ集合の可算和も再びカラテオドリである。
:::
::::
:::::

```leanDecl
MTI.Real.isCaratheodory_disjointed
MTI.Real.isCaratheodory_iUnion_of_disjoint
MTI.Real.isCaratheodory_iUnion
```

:::::theoremBox "Continuity from below" (ja := "下からの連続性")
::::localized
Let $`A_0, A_1, \dots \subset \mathbb{R}` be a monotonically increasing sequence of
Carathéodory sets. Then
$$`
  m\left( \bigcup_{n \in \mathbb{N}} A_n \right)
    = \sup_{n \in \mathbb{N}} m(A_n).`
:::locale "ja"
$`A_0, A_1, \dots \subset \mathbb{R}` をカラテオドリ集合の単調増大列とする。
このとき
$$`
  m\left( \bigcup_{n \in \mathbb{N}} A_n \right)
    = \sup_{n \in \mathbb{N}} m(A_n).
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_c_iUnion_of_monotone
```

:::::theoremBox "Countable additivity" (ja := "可算加法性")
::::localized
Let $`A_0, A_1, \dots \subset \mathbb{R}` be a sequence of pairwise disjoint Carathéodory sets. Then
$$`
  m\left( \bigcup_{n \in \mathbb{N}} A_n \right)
    = \sum_{n \in \mathbb{N}} m(A_n).`
:::locale "ja"
$`A_0, A_1, \dots \subset \mathbb{R}` を互いに交わらないカラテオドリ集合の列とする。
このとき
$$`
  m\left( \bigcup_{n \in \mathbb{N}} A_n \right)
    = \sum_{n \in \mathbb{N}} m(A_n).
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_c_iUnion
```
