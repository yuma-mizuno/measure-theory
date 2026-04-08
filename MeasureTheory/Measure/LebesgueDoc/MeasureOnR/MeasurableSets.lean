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
Measurable subsets of $`\mathbb{R}` are generated from the half-lines
$`[a,\infty)` together with the empty set by closing under complements and
countable unions.
:::locale "ja"
$`\mathbb{R}` の可測部分集合は、半直線 $`[a,\infty)` と空集合から出発して、補集合と可算和で閉じるようにして生成される。
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
