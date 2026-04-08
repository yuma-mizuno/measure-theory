import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.MeasurableSpace"
lebesgue_doc_module MeasureTheory.Lean.MeasurableSpace

open Verso Genre Manual

#doc (Manual) "Measurable Spaces" =>

%%%
file := "Measurable-Spaces"
tag := "measurable-spaces"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "可測空間")
:::

:::::definitionBox "Measurable Space" (ja := "可測空間") (tag := "def-measurable-space")
::::localized
Let $`X` be a set.
A sigma-algebra on $`X` is a collection $`\mathcal{M} \subseteq \mathcal{P}(X)` such that

1. $`\emptyset \in \mathcal{M}`,
2. if $`A \in \mathcal{M}`, then $`A^c \in \mathcal{M}`,
3. if $`A_0, A_1, \dots \in \mathcal{M}`, then $`\bigcup_{n \in \mathbb{N}} A_n \in \mathcal{M}`.

A set $`X` equipped with a sigma-algebra $`\mathcal{M}` is called a _measurable space_.
:::locale "ja"
$`X` を集合とする。
$`X` 上の σ-代数とは、$`\mathcal{P}(X)` の部分集合 $`\mathcal{M} \subseteq \mathcal{P}(X)` であって、次を満たすものをいう。

1. $`\emptyset \in \mathcal{M}` である。
2. $`A \in \mathcal{M}` ならば $`A^c \in \mathcal{M}` である。
3. $`A_0, A_1, \dots \in \mathcal{M}` ならば $`\bigcup_{n \in \mathbb{N}} A_n \in \mathcal{M}` である。

σ-代数 $`\mathcal{M}` を備えた集合 $`X` を _可測空間_ という。
:::
::::
:::::

```leanDecl
MTI.MeasurableSpace
```

:::::definitionBox "Measurable Set" (ja := "可測集合") (tag := "def-measurable-set")
::::localized
If $`X` is a measurable space,
its sigma-algebra is denoted by $`\mathcal{M}(X)`.
A subset $`A \subseteq X` is called _measurable_
if $`A \in \mathcal{M}(X)`.
:::locale "ja"
$`X` を可測空間とする。
その σ-代数を $`\mathcal{M}(X)` と書く。
部分集合 $`A \subseteq X` が _可測_ であるとは、$`A \in \mathcal{M}(X)` が成り立つことをいう。
:::
::::
:::::

```leanDecl
MTI.MeasurableSet
```

:::::definitionBox "Measurable Map" (ja := "可測写像")
::::localized
Let $`X` and $`Y` be measurable spaces.
A function $`f : X \to Y` is called _measurable_ if for any measurable set $`B \subseteq Y`,
the preimage $`f^{-1}(B) \subseteq X` is measurable.
:::locale "ja"
$`X` と $`Y` を可測空間とする。
写像 $`f : X \to Y` が _可測_ であるとは、任意の可測集合 $`B \subseteq Y` に対して、その逆像
$`f^{-1}(B) \subseteq X` が可測であることをいう。
:::
::::
:::::

```leanDecl
MTI.Measurable
```
