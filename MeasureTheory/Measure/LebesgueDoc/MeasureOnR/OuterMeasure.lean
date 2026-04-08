import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lebesgue.OuterMeasure"
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.OuterMeasure

open Verso Genre Manual

#doc (Manual) "Measure on the Real Line" =>

%%%
file := "Measure-on-the-Real-Line"
tag := "measure-on-the-real-line"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "実数直線上の測度")
:::

:::::definitionBox "Lebesgue outer measure" (ja := "ルベーグ外測度") (tag := "def-lebesgue-outer-measure")
::::localized
The _Lebesgue outer measure_ of a set $`A \subseteq \mathbb{R}` is defined by
$$`
  m (A) \coloneqq
  \inf_{a : \mathbb{N} \to \mathbb{R},\, b : \mathbb{N} \to \mathbb{R},\,
    A \subseteq \bigcup_{n} (a_n, b_n)}
  \sum_{n \in \mathbb{N}} (b_n - a_n)^+ \ \in \ [0, \infty],`
where $`x^+ \coloneqq \max(x, 0) \in [0, \infty]` for $`x \in \mathbb{R}`.

:::locale "ja"
集合 $`A \subseteq \mathbb{R}` の _ルベーグ外測度_ を次で定義する:
$$`
  m (A) \coloneqq
  \inf_{a : \mathbb{N} \to \mathbb{R},\, b : \mathbb{N} \to \mathbb{R},\,
    A \subseteq \bigcup_{n} (a_n, b_n)}
  \sum_{n \in \mathbb{N}} (b_n - a_n)^+ \ \in \ [0, \infty].`
ここで、$`x \in \mathbb{R}` に対して $`x^+ \coloneqq \max(x, 0) \in [0, \infty]` とする。
:::
::::
:::::

```leanDecl
MTI.Real.measure
```

:::::lemmaBox
::::localized
If
$`A \subseteq \bigcup_{i \in \mathbb{N}} (a_i, b_i)`,
then $`m (A) \le \sum_{n \in \mathbb{N}} (b_n - a_n)^+`.
:::locale "ja"
$`A \subseteq \bigcup_{i \in \mathbb{N}} (a_i, b_i)` ならば、
$`m (A) \le \sum_{n \in \mathbb{N}} (b_n - a_n)^+` が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_le
```

:::::theoremBox "The measure of an interval is its length" (ja := "区間の測度は長さに等しい")
::::localized
For any $`a, b \in \mathbb{R}`,
we have $`m([a,b]) = (b-a)^+`.
:::locale "ja"
任意の $`a, b \in \mathbb{R}` に対して、$`m([a,b]) = (b-a)^+` が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_Icc_le
MTI.Real.measure_Icc
```

:::::lemmaBox
::::localized
  1. $`m(\emptyset) = 0`.
  2. For $`A, B \subseteq \mathbb{R}` with $`A \subseteq B`, we have $`m(A) \leq m(B)`.
  3. For $`A_0, A_1, \dots \subseteq \mathbb{R}`, we have
    $$`
      m\left( \bigcup_{n \in \mathbb{N}} A_n \right)
        \leq \sum_{n \in \mathbb{N}} m(A_n).`
:::locale "ja"
  1. $`m(\emptyset) = 0` である。
  2. $`A, B \subseteq \mathbb{R}` が $`A \subseteq B` を満たすなら、$`m(A) \leq m(B)` が成り立つ。
  3. $`A_0, A_1, \dots \subseteq \mathbb{R}` に対して、
    $$`
      m\left( \bigcup_{n \in \mathbb{N}} A_n \right)
        \leq \sum_{n \in \mathbb{N}} m(A_n).
    `
    が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.measure_empty
MTI.Real.measure_mono
MTI.Real.measure_iUnion_le
```
