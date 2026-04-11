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
MTI.Real.MeasurableSet.translate
MTI.Real.measure_translate_le
MTI.Real.measure_translate
```

:::::definitionBox "Vitali Set" (ja := "ヴィタリ集合")
::::localized
We define a set $`V \subseteq \mathbb{R}` by choosing one representative from each
rational-translation equivalence class in $`[0,1]`.
:::locale "ja"
$`[0,1]` の点を有理数平行移動による同値類ごとにひとつずつ選んで、
集合 $`V \subseteq \mathbb{R}` を定める。
:::
::::
:::::

```leanDecl
MTI.Real.vitaliSet
```

:::::lemmaBox
::::localized
The set $`V` defined above satisfies $`V \subseteq [0,1]`, and it contains exactly one
representative from each rational-translation equivalence class in $`[0,1]`.
:::locale "ja"
上で定めた集合 $`V` は $`V \subseteq [0,1]` を満たし、さらに $`[0,1]` の各点の
有理数平行移動による同値類からちょうどひとつずつ代表元を含む。
:::
::::
:::::

```leanDecl
MTI.Real.vitaliSet_subset_Icc_zero_one
MTI.Real.existsUnique_mem_vitaliSet_rationalRel
```

::::localized
A set with the properties stated in the lemma above is called a _Vitali set_.
The set $`V` is a Vitali set defined using the axiom of choice.
:::locale "ja"
上の補題で述べた性質を持つ集合を_ヴィタリ集合_といいます。
$`V` はヴィタリ集合を選択公理を用いて定義したものです。
:::
::::

:::::lemmaBox
::::localized
The set $`V` satisfies
$$`m(V) \neq 0.`
:::locale "ja"
$$`
  m(V) \neq 0
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.Icc_zero_one_subset_iUnion_translate_vitaliSet
MTI.Real.measure_vitaliSet_ne_zero
```

:::::lemmaBox
::::localized
For every measurable set $`E \subseteq \mathbb{R}`, if $`E \subseteq V`, then
$$`m(E) = 0.`
:::locale "ja"
任意の可測集合 $`E \subseteq \mathbb{R}` について、$`E \subseteq V` ならば
$$`
  m(E) = 0
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.disjoint_translate_of_subset_vitaliSet
MTI.Real.measure_eq_zero_of_measurableSet_subset_vitaliSet
```

::::localized
Taken together, the previous two lemmas show that the set $`V` cannot be measurable.
:::locale "ja"
以上の二つの補題を合わせると、集合 $`V` は可測ではありえないことがわかります。
:::
::::

:::::theoremBox "Existence of Nonmeasurable Sets" (ja := "非可測集合の存在")
::::localized
The set $`V` is not measurable.
:::locale "ja"
集合 $`V` は可測ではない。
:::
::::
:::::

```leanDecl
MTI.Real.not_measurableSet_vitaliSet
```

:::::lemmaBox
::::localized
The set $`[0,1] \setminus V` satisfies
$$`m([0,1] \setminus V) = 1.`
:::locale "ja"
$$`
  m([0,1] \setminus V) = 1
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_compl_vitaliSet_eq_one
```

:::::lemmaBox
::::localized
The decomposition of $`[0,1]` by $`V` satisfies
$$`m([0,1]) \neq m(V) + m([0,1] \setminus V).`
:::locale "ja"
集合 $`V` による $`[0,1]` の分解について
$$`
  m([0,1]) \neq m(V) + m([0,1] \setminus V)
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.vitaliSet_compl_nonadditive
```

::::localized
In particular, there exist disjoint sets for which additivity fails.
:::locale "ja"
したがって、加法性を満たさない交わらない集合の組が存在します。
:::
::::

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
