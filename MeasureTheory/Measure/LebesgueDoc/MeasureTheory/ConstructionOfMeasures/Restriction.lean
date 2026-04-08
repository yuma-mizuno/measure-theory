import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Measures.Restriction"
lebesgue_doc_module MeasureTheory.Lean.Measures.Restriction
open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Restriction" =>

%%%
file := "Restriction"
tag := "restriction"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "制限測度")
:::

:::::definitionBox
::::localized
Let $`X` be a measurable space, let $`\mu` be a measure on $`X`, and let $`A \subseteq X` be
measurable.
The _restriction_ of $`\mu` to $`A`, denoted by $`\mu|_A`, is the measure defined by
$$`
  (\mu|_A)(B) \coloneqq \mu(A \cap B)
`
for measurable sets $`B \subseteq X`.
:::locale "ja"
$`X` を可測空間とし、$`\mu` を $`X` 上の測度、$`A \subseteq X` を可測集合とする。
$`\mu` の $`A` への _制限_ を $`\mu|_A` と書き、任意の可測集合 $`B \subseteq X` に対して
$$`
  (\mu|_A)(B) \coloneqq \mu(A \cap B)
`
で定義される測度として定める。
:::
::::
:::::

```leanDecl
MTI.Measure.restrict
MTI.Measure.restrict_apply
```

::::localized
Conceptually, $`\mu|_A` forgets everything outside $`A` and measures only the portion of a set
that remains inside $`A`.
:::locale "ja"
概念的には、$`\mu|_A` は $`A` の外側の情報を捨て、集合のうち $`A` の内側に残る部分だけを測ります。
:::
::::

:::::lemmaBox
::::localized
The definition is compatible with the associated outer measure:
$$`
  (\mu|_A)^{*} (B) = \mu^{*} (A \cap B)
`
for any subset $`B \subseteq X` (not necessarily measurable).

Here $`\mu^{*}` denotes the outer measure associated with $`\mu`.
:::locale "ja"
この定義は、付随する外測度と両立している:
$$`
  (\mu|_A)^{*} (B) = \mu^{*} (A \cap B)
`
が任意の部分集合 $`B \subseteq X`（可測でなくてもよい）に対して成り立つ。

ここで $`\mu^{*}` は $`\mu` に付随する外測度を表す。
:::
::::
:::::

```leanDecl
MTI.Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict
```

:::::lemmaBox
::::localized
If $`A` is measurable, then integrating against the restricted measure is the same as inserting
the indicator of $`A` into the integrand:
$$`
  \underline{\int}_{x \in X} f(x)\,d(\mu|_A)
    =
  \underline{\int}_{x \in X} 1_A(x) \cdot f(x)\,d\mu.
`
:::locale "ja"
$`A` が可測ならば、制限測度に関する積分は被積分関数に $`A` の指示関数を掛けることと同じである:
$$`
  \underline{\int}_{x \in X} f(x)\,d(\mu|_A)
    =
  \underline{\int}_{x \in X} 1_A(x) \cdot f(x)\,d\mu.
`
:::
::::
:::::

```leanDecl
MTI.lintegral_indicator_le
MTI.lintegral_restrict
```
