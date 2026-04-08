import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.AE"
lebesgue_doc_module MeasureTheory.Lean.AE
lebesgue_doc_module Mathlib.MeasureTheory.OuterMeasure.AE

open Verso Genre Manual

#doc (Manual) "Almost Everywhere" =>

%%%
file := "Almost-Everywhere-for-Integrals"
tag := "almost-everywhere-for-integrals"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "ほとんど至る所")
:::

::::localized
Let $`X` be a measurable space, and let $`\mu` be a measure on $`X`.
:::locale "ja"
$`X` を可測空間とし、$`\mu` を $`X` 上の測度とします。
:::
::::

:::::definitionBox
::::localized
Let $`P(x)` be a property of points $`x \in X`.
We say that $`P` holds _almost everywhere_ with respect to $`\mu`
(or $`P(x)` holds for $`\mu`-a.e. $`x \in X`)
if the exceptional set has outer measure zero:
$$`
  \mu^* (\{x \in X \mid \neg P(x)\}) = 0.`
Here $`\mu^{*}` denotes the
{ref "def-outer-measure-associated-with-a-measure"}[outer measure associated with] $`\mu`.
:::locale "ja"
$`P(x)` を点 $`x \in X` に関する性質とする。
$`P` が $`\mu` に関して _ほとんど至る所_ 成り立つ
（あるいは $`P(x)` が $`\mu`-a.e. $`x \in X` で成り立つ）とは、
例外集合の外測度が $`0` であること、すなわち
$$`
  \mu^* (\{x \in X \mid \neg P(x)\}) = 0
`
が成り立つことをいう。
ここで $`\mu^{*}` は$`\mu` に
{ref "def-outer-measure-associated-with-a-measure"}[付随する外測度]
を表す。
:::
::::
:::::

```leanDecl
MeasureTheory.ae_iff
```

:::::lemmaBox
::::localized
Let $`f, g : X \to [0,\infty]`.
If $`f = g` almost everywhere, then their lower Lebesgue integrals are equal:
$$`
  \underline{\int}_{x \in X} f(x)\,d\mu
    =
  \underline{\int}_{x \in X} g(x)\,d\mu.`
:::locale "ja"
$`f, g : X \to [0,\infty]` とする。
$`f = g` がほとんど至る所成り立つならば、それらの下ルベーグ積分は等しい:
$$`
  \underline{\int}_{x \in X} f(x)\,d\mu
    =
  \underline{\int}_{x \in X} g(x)\,d\mu.
`
:::
::::
:::::

```leanDecl
MTI.SimpleFunc.measure_preimage_singleton_congr_ae
MTI.lintegral_mono_ae
MTI.lintegral_congr_ae
```
