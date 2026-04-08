import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Measure"
lebesgue_doc_module MeasureTheory.Lean.Measure

open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Measures" =>

%%%
file := "Measures"
tag := "measures"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "測度")
:::

# Measure

:::localizedPart (ja := "測度")
:::

:::::definitionBox "Measure" (ja := "測度") (tag := "def-measure")
::::localized
Let $`X` be a measurable space.
A _measure_ on $`X` consists of a function assigning to each measurable set $`A \subseteq X` a value
in $`[0,\infty]` such that

1. $`\mu(\emptyset) = 0`,
2. if $`A` and $`B` are measurable and disjoint, then
   $`\mu(A \cup B) = \mu(A) + \mu(B)`,
3. if $`A_0 \subseteq A_1 \subseteq \cdots` is an increasing sequence of measurable sets, then
   $`\mu\left(\bigcup_{n \in \mathbb{N}} A_n\right) = \sup_{n \in \mathbb{N}} \mu(A_n)`.
:::locale "ja"
$`X` を可測空間とする。
$`X` 上の _測度_ とは、各可測集合 $`A \subseteq X` に $`[0,\infty]` の値を対応させる関数であって、次を満たすものをいう。

1. $`\mu(\emptyset) = 0` である。
2. $`A` と $`B` が可測で交わりを持たなければ、$`\mu(A \cup B) = \mu(A) + \mu(B)` である。
3. $`A_0 \subseteq A_1 \subseteq \cdots` が可測集合の増大列ならば、
   $`\mu\left(\bigcup_{n \in \mathbb{N}} A_n\right) = \sup_{n \in \mathbb{N}} \mu(A_n)` である。
:::
::::
:::::

```leanDecl
MTI.Measure
```

:::::theoremBox "Countable Additivity" (ja := "可算加法性")
::::localized
Let $`A_0, A_1, \dots \subseteq X` be pairwise disjoint measurable sets.
Then
$$`
  \mu\left(\bigcup_{n \in \mathbb{N}} A_n\right)
    =
  \sum_{n \in \mathbb{N}} \mu(A_n).
`
:::locale "ja"
$`A_0, A_1, \dots \subseteq X` を互いに交わらない可測集合の列とする。
このとき
$$`
  \mu\left(\bigcup_{n \in \mathbb{N}} A_n\right)
    =
  \sum_{n \in \mathbb{N}} \mu(A_n).
`
:::
::::
:::::

```leanDecl
MTI.Measure.iUnion_of_disjoint'
```

:::::theoremBox "Measure from Countable Additivity" (ja := "可算加法性から作る測度")
::::localized
Conversely, suppose that a function $`\mu(A)` is given on measurable sets and satisfies:

1. $`\mu(\emptyset) = 0`.

2. For every sequence of measurable sets $`A_0, A_1, \dots` that is pairwise disjoint,
   $$`
     \mu\left(\bigcup_{n \in \mathbb{N}} A_n\right)
       =
     \sum_{n \in \mathbb{N}} \mu(A_n).
   `

Then $`\mu` is a measure.
:::locale "ja"
逆に、可測集合上の関数 $`\mu(A)` が与えられていて、次を満たすとする。

1. $`\mu(\emptyset) = 0` である。

2. 互いに交わらない可測集合の列 $`A_0, A_1, \dots` に対して常に
   $$`
     \mu\left(\bigcup_{n \in \mathbb{N}} A_n\right)
       =
     \sum_{n \in \mathbb{N}} \mu(A_n).
   `
   が成り立つ。

このとき $`\mu` は測度である。
:::
::::
:::::

```leanDecl
MTI.Measure.iUnion_of_disjoint_countable
MTI.Measure.union_of_countablyAdditive
MTI.Measure.accumulate_eq_sum_of_countablyAdditive
MTI.Measure.iUnion_of_monotone_of_countablyAdditive
MTI.Measure.ofCountablyAdditive
```
