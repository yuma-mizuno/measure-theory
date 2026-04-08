import MeasureTheory.Lean.Lebesgue.MeasurableSets
import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lebesgue.MeasurableSets"
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.MeasurableSets

open Verso Genre Manual

#doc (Manual) "Measurable Sets" =>

%%%
file := "Measurable-Sets"
tag := "measurable-sets"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "可測集合")
:::

:::::definitionBox
::::localized
We define inductively the notion of a subset $`A \subseteq \mathbb{R}` being
_(Borel) measurable_ as follows:
1. For every $`a \in \mathbb{R}`, the half-line $`[a,\infty)` is measurable.
2. The empty set $`\emptyset` is measurable.
3. If $`A` is measurable, then its complement $`A^c` is measurable.
4. If $`A_0, A_1, \dots` are measurable, then $`\bigcup_{n \in \mathbb{N}} A_n`
   is measurable.
:::locale "ja"
部分集合 $`A \subseteq \mathbb{R}` が _（ボレル）可測_ であるという概念を、
次のように帰納的に定義する。
1. 任意の $`a \in \mathbb{R}` に対して、半直線 $`[a,\infty)` は可測である。
2. 空集合 $`\emptyset` は可測である。
3. $`A` が可測ならば、その補集合 $`A^c` も可測である。
4. $`A_0, A_1, \dots` が可測ならば、$`\bigcup_{n \in \mathbb{N}} A_n` も可測である。
:::
::::
:::::

```leanDecl
MTI.Real.MeasurableSet
```

:::::lemmaBox
::::localized
The empty set and the whole space $`\mathbb{R}` are measurable.
:::locale "ja"
空集合と全体集合 $`\mathbb{R}` は可測である。
:::
::::
:::::

```leanDecl
MTI.Real.MeasurableSet.empty
MTI.Real.MeasurableSet.univ
```

:::::lemmaBox
::::localized
Countable unions and intersections of measurable sets are measurable.
:::locale "ja"
可測集合の可算和と可算共通部分は可測である。
:::
::::
:::::

```leanDecl
MTI.Real.MeasurableSet.iUnion
MTI.Real.MeasurableSet.iInter
```

:::::lemmaBox
::::localized
Unions, complements, and intersections of measurable sets are measurable.
:::locale "ja"
可測集合の和集合、補集合、共通部分は可測である。
:::
::::
:::::

```leanDecl
MTI.Real.MeasurableSet.union
MTI.Real.MeasurableSet.compl
MTI.Real.MeasurableSet.inter
```

:::::lemmaBox
::::localized
The intervals
$`[a,\infty)`, $`(-\infty,a)`, $`(a,\infty)`, $`(-\infty,a]`,
$`(a,b]`, $`[a,b)`, $`[a,b]`, $`(a,b)`
and the singleton $`\{a\}` are measurable.
:::locale "ja"
区間
$`[a,\infty)`, $`(-\infty,a)`, $`(a,\infty)`, $`(-\infty,a]`,
$`(a,b]`, $`[a,b)`, $`[a,b]`, $`(a,b)`
および一点集合 $`\{a\}` は可測である。
:::
::::
:::::

```leanDecl
MTI.Real.measurableSet_Ici
MTI.Real.measurableSet_Iio
MTI.Real.measurableSet_Ioi
MTI.Real.measurableSet_Iic
MTI.Real.measurableSet_Ioc
MTI.Real.measurableSet_Ico
MTI.Real.measurableSet_Icc
MTI.Real.measurableSet_Ioo
MTI.Real.measurableSet_singleton
```
