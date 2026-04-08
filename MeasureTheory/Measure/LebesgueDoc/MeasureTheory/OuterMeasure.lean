import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Measure"
lebesgue_doc_module MeasureTheory.Lean.Measure

open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Outer Measure" =>

%%%
file := "Outer-Measure"
tag := "outer-measure"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "測度に付随する外測度")
:::

:::::definitionBox "Outer measure associated with a measure" (ja := "測度に付随する外測度") (tag := "def-outer-measure-associated-with-a-measure")
::::localized
Let $`X` be a measurable space, and let $`\mu` be a measure on $`X`.
We define a function $`\mu^* : \mathcal{P}(X) \to [0,\infty]` by
$$`
  \mu^*(A) \coloneqq \inf_{\substack{B \subseteq X,\\ \text{$B$ is measurable},\, A \subseteq B}}
    \mu(B)
`
for any $`A \subseteq X`.
The function $`\mu^*` is called the _outer measure associated with $`\mu`_.
:::locale "ja"
$`X` を可測空間とし、$`\mu` を $`X` 上の測度とする。
このとき関数 $`\mu^* : \mathcal{P}(X) \to [0,\infty]` を
$$`
  \mu^*(A) \coloneqq \inf_{\substack{B \subseteq X,\\ \text{$B$ is measurable},\, A \subseteq B}}
    \mu(B)
`
によって定める。ただし $`A \subseteq X` は任意とする。
この関数 $`\mu^*` を _$`\mu` に付随する外測度_ という。
:::
::::
:::::

```leanDecl
MTI.Measure.toOuterMeasure
```

:::::lemmaBox
::::localized
If $`A \subseteq X` is measurable, the extension to all subsets agrees with the original value:
$$`
  \mu^*(A) = \mu(A).
`
:::locale "ja"
$`A \subseteq X` が可測ならば、全ての部分集合へ拡張した値は元の値と一致する:
$$`
  \mu^*(A) = \mu(A).
`
:::
::::
:::::

```leanDecl
MTI.Measure.toFun_apply
```

:::::lemmaBox
::::localized
The outer measure associated with a measure $`\mu` on $`X` satisfies the following properties:

1. We have

    $$`
      \mu^*(\emptyset) = 0.
    `

2. If $`A \subseteq B`, then

    $$`
      \mu^*(A) \le \mu^*(B).
    `

3. For any sequence of subsets $`A_0, A_1, \dots \subseteq X`,

    $$`
      \mu^*\left(\bigcup_{n \in \mathbb{N}} A_n\right)
        \le
      \sum_{n \in \mathbb{N}} \mu^*(A_n).
    `
:::locale "ja"
$`X` 上の測度 $`\mu` に付随する外測度は、次の 3 つの性質を満たす。

1. $`\mu^*(\emptyset) = 0`

2. $`A \subseteq B` ならば $`\mu^*(A) \le \mu^*(B)`。

3. 任意の部分集合列 $`A_0, A_1, \dots \subseteq X` に対して

    $$`
      \mu^*\left(\bigcup_{n \in \mathbb{N}} A_n\right)
        \le
      \sum_{n \in \mathbb{N}} \mu^*(A_n).
    `
:::
::::
:::::

```leanDecl
MTI.Measure.empty
MTI.Measure.mono
MTI.Measure.iUnion_le
```

:::::lemmaBox
::::localized
If $`A \subseteq X` is measurable, then $`A` is Carathéodory with respect to the outer measure
$`\mu^*` associated with $`\mu`. In other words, for every subset $`B \subseteq X`,
$$`
  \mu^*(B)
    =
  \mu^*(B \cap A)
    +
  \mu^*(B \setminus A).
`
:::locale "ja"
$`A \subseteq X` が可測ならば、$`A` は $`\mu` に付随する外測度 $`\mu^*` に関してカラテオドリである。
すなわち、任意の部分集合 $`B \subseteq X` に対して
$$`
  \mu^*(B)
    =
  \mu^*(B \cap A)
    +
  \mu^*(B \setminus A).
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Measure.toOuterMeasure_caratheodory
```

:::::lemmaBox
::::localized
Conversely, suppose that a function $`\bar{\mu} : \mathcal{P}(X) \to [0,\infty]` satisfies:

1. $`\bar{\mu}(\emptyset) = 0`.

2. If $`A \subseteq B`, then
   $$`
     \bar{\mu}(A) \le \bar{\mu}(B).
   `

3. For any sequence of subsets $`A_0, A_1, \dots \subseteq X`,
   $$`
     \bar{\mu}\left(\bigcup_{n \in \mathbb{N}} A_n\right)
       \le
     \sum_{n \in \mathbb{N}} \bar{\mu}(A_n).
   `

Suppose moreover that every measurable set $`A \subseteq X` is Carathéodory, meaning that for
every subset $`B \subseteq X`,
$$`
  \bar{\mu}(B)
    =
  \bar{\mu}(B \cap A)
    +
  \bar{\mu}(B \setminus A).
`
Then restricting $`\bar{\mu}` to measurable sets defines a measure on $`X`.
:::locale "ja"
逆に、関数 $`\bar{\mu} : \mathcal{P}(X) \to [0,\infty]` が次を満たすとする。

1. $`\bar{\mu}(\emptyset) = 0` である。

2. $`A \subseteq B` ならば
   $$`
     \bar{\mu}(A) \le \bar{\mu}(B).
   `
   が成り立つ。

3. 任意の部分集合列 $`A_0, A_1, \dots \subseteq X` に対して
   $$`
     \bar{\mu}\left(\bigcup_{n \in \mathbb{N}} A_n\right)
       \le
     \sum_{n \in \mathbb{N}} \bar{\mu}(A_n).
   `
   が成り立つ。

さらに、任意の可測集合 $`A \subseteq X` がカラテオドリであるとする。すなわち、任意の部分集合 $`B \subseteq X` に対して
$$`
  \bar{\mu}(B)
    =
  \bar{\mu}(B \cap A)
    +
  \bar{\mu}(B \setminus A).
`
が成り立つとする。
このとき $`\bar{\mu}` を可測集合に制限すると、$`X` 上の測度が定まる。
:::
::::
:::::

```leanDecl
MTI.Measure.ofOuterMeasure
```
