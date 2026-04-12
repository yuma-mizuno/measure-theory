import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lebesgue.FailureOfAdditivity"
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.FailureOfAdditivity

open Verso Genre Manual

#doc (Manual) "Failure of Additivity" =>

%%%
file := "Failure-of-Additivity"
tag := "failure-of-additivity"
%%%

:::localizedPart (ja := "加法性の破綻")
:::

:::lebesgueDocSetup
:::

::::localized
We show that there exist a pair of sets that do not satisfy additivity.
:::locale "ja"
加法性を満たさない集合の組が存在することを見ます。
:::
::::

::::localized
As preparation, we first recall the translation invariance of measure.
:::locale "ja"
準備として、まず測度の平行移動不変性を確認します。
:::
::::

:::::lemmaBox "Translation Invariance" (ja := "平行移動不変性")
::::localized
For every set $`A \subseteq \mathbb{R}` and every $`c \in \mathbb{R}`,
$$`m(\{x \mid x - c \in A\}) = m(A).`
:::locale "ja"
任意の集合 $`A \subseteq \mathbb{R}` と任意の $`c \in \mathbb{R}` に対して
$$`
  m(\{x \mid x - c \in A\}) = m(A)
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.translate
MTI.Real.measure_translate_le
MTI.Real.measure_translate
```

:::::definitionBox "Vitali Set" (ja := "ヴィタリ集合")
::::localized
A set $`A \subseteq \mathbb{R}` is called a _Vitali set_ if
$`A \subseteq [0,1]` and, for every $`x \in \mathbb{R}` there exists a unique rational number
$`q` such that $`x - q \in A`.
:::locale "ja"
集合 $`A \subseteq \mathbb{R}` が_ヴィタリ集合_であるとは、
$`A \subseteq [0,1]` を満たし、さらに任意の $`x \in \mathbb{R}` に対して
$`x - q \in A` を満たす有理数 $`q` がただひとつ存在することをいう。
:::
::::
:::::

```leanDecl
MTI.Real.IsVitali
```

:::::lemmaBox
::::localized
If $`A` is a Vitali set, then
$$`m(A) \neq 0.`
:::locale "ja"
$`A` がヴィタリ集合ならば、
$$`
  m(A) \neq 0
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.IsVitali.Icc_zero_one_subset_iUnion_translate
MTI.Real.IsVitali.measure_ne_zero
```

:::::lemmaBox
::::localized
If $`A` is a Vitali set and $`E \subseteq A` is measurable, then
$$`m(E) = 0.`
:::locale "ja"
$`A` がヴィタリ集合で、$`E \subseteq A` が可測ならば、
$$`
  m(E) = 0
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.IsVitali.measure_eq_zero_of_measurableSet_subset
```

::::localized
Taken together, the previous two lemmas show that a Vitali set cannot be measurable.
:::locale "ja"
以上の二つの補題を合わせると、ヴィタリ集合は可測になりえないとわかります。
:::
::::

:::::theoremBox "Nonmeasurability of Vitali Sets" (ja := "ヴィタリ集合は非可測")
::::localized
If $`A` is a Vitali set, then $`A` is not measurable.
:::locale "ja"
$`A` がヴィタリ集合ならば、$`A` は可測ではない。
:::
::::
:::::

```leanDecl
MTI.Real.IsVitali.not_measurableSet
```

:::::lemmaBox
::::localized
If $`A` is a Vitali set, then
$$`m([0,1] \setminus A) = 1.`
:::locale "ja"
$`A` がヴィタリ集合ならば、
$$`
  m([0,1] \setminus A) = 1
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.IsVitali.measure_compl_eq_one
```

:::::theoremBox "Failure of Additivity for Vitali Sets" (ja := "ヴィタリ集合に対する加法性の破綻")
::::localized
If $`A` is a Vitali set, then
$$`m([0,1]) \neq m(A) + m([0,1] \setminus A).`
:::locale "ja"
$`A` がヴィタリ集合ならば、
$$`
  m([0,1]) \neq m(A) + m([0,1] \setminus A)
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.IsVitali.compl_nonadditive
```

::::localized
To deduce actual existence statements, it remains only to construct one Vitali set.
:::locale "ja"
これで、実際の存在定理を得るためにはヴィタリ集合をひとつ構成すれば十分です。
:::
::::

:::::definitionBox "Existence of Vitali Sets" (ja := "ヴィタリ集合の存在")
::::localized
Consider the equivalence relation on $`\mathbb{R}` given by rational translation.
Every equivalence class meets $`[0,1]`, so by the axiom of choice we may choose one point in
$`[0,1]` from each class. Let $`V \subseteq \mathbb{R}` be the set of all chosen representatives.
:::locale "ja"
$`\mathbb{R}` 上の有理数平行移動による同値関係を考える。各同値類は
$`[0,1]` と交わるので、選択公理により各同値類から $`[0,1]` に入る点を
ひとつずつ選ぶことができる。そのようにして選んだ代表元全体からなる集合を
$`V \subseteq \mathbb{R}` とする。
:::
::::
:::::

```leanDecl
MTI.Real.exists_rationalRel_mem_Icc_zero_one
MTI.Real.exists_subtype_mk_eq_quotient
MTI.Real.chosenVitaliPoint
MTI.Real.chosenVitali
```

:::::lemmaBox
::::localized
The set $`V` defined above is a Vitali set.
:::locale "ja"
上で定義した集合 $`V` はヴィタリ集合である。
:::
::::
:::::

```leanDecl
MTI.Real.chosenVitali_subset_Icc_zero_one
MTI.Real.existsUnique_rational_chosenVitali
MTI.Real.isVitali_chosenVitali
```

:::::theoremBox "Existence of Nonmeasurable Sets" (ja := "非可測集合の存在")
::::localized
There exists a set $`A \subseteq \mathbb{R}` that is not measurable.
:::locale "ja"
可測でない集合 $`A \subseteq \mathbb{R}` が存在する。
:::
::::
:::::

```leanDecl
MTI.Real.exists_not_measurableSet
```

:::::theoremBox "Failure of Additivity" (ja := "加法性の破綻")
::::localized
There exist disjoint sets $`A, B \subseteq \mathbb{R}` such that
$$`m(A \cup B) \neq m(A) + m(B).`
:::locale "ja"
交わらない集合 $`A, B \subseteq \mathbb{R}` であって、
$$`
  m(A \cup B) \neq m(A) + m(B)
`
を満たすものが存在する。
:::
::::
:::::

```leanDecl
MTI.Real.exists_disjoint_nonadditive
```
