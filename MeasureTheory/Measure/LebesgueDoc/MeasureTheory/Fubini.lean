import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Fubini"
lebesgue_doc_module MeasureTheory.Lean.Fubini
open Verso Genre Manual

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Fubini's Theorem" =>

%%%
file := "Fubinis-Theorem"
tag := "fubinis-theorem"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "フビニの定理")
:::

::::localized
Let $`X` and $`Y` be measurable spaces, let $`\mu` be a measure on $`X`,
and let $`\nu` be a measure on $`Y`.
:::locale "ja"
$`X` と $`Y` を可測空間とし、$`\mu` を $`X` 上の測度、$`\nu` を $`Y` 上の測度とします。
:::
::::

:::::lemmaBox
::::localized
Let $`f : X \times Y \to \mathbb{R}` be integrable with respect to $`\mu \times \nu`.
Suppose that $`\nu` is S-finite.
Then for $`\mu`-almost every $`x \in X`, the partial application $`f (x, -) : Y \to \mathbb{R}` is integrable
with respect to $`\nu`.
:::locale "ja"
$`f : X \times Y \to \mathbb{R}` が $`\mu \times \nu` に関して可積分であるとする。
$`\nu` は S-有限であると仮定する。
このとき $`\mu`-ほとんど至る所の $`x \in X` に対して、部分適用 $`f (x, -) : Y \to \mathbb{R}` は
$`\nu` に関して可積分である。
:::
::::
:::::

```leanDecl
MTI.ae_integrable_sections
```

:::::lemmaBox
::::localized
Let $`f : X \times Y \to \mathbb{R}` be integrable with respect to $`\mu \times \nu`.
Suppose that $`\nu` is S-finite.
Then the function
$$`
  x \longmapsto \int_{y \in Y} f^+(x,y)\,d\nu`
from $`X` to $`\mathbb{R}` is integrable with respect to $`\mu`.
:::locale "ja"
$`f : X \times Y \to \mathbb{R}` が $`\mu \times \nu` に関して可積分であるとする。
$`\nu` は S-有限であると仮定する。
このとき関数
$$`
  x \longmapsto \int_{y \in Y} f^+(x,y)\,d\nu
`
は $`X` から $`\mathbb{R}` への関数として $`\mu` に関して可積分である。
:::
::::
:::::

```leanDecl
MTI.measurable_integral_section_posPart
MTI.lintegral_integral_section_posPart_ne_top
MTI.integrable_integral_section_posPart
```

:::::lemmaBox
::::localized
Let $`f : X \times Y \to \mathbb{R}` be integrable with respect to $`\mu \times \nu`.
Suppose that $`\nu` is S-finite.
Then the function
$$`
  x \longmapsto \int_{y \in Y} f^-(x,y)\,d\nu`
from $`X` to $`\mathbb{R}` is integrable with respect to $`\mu`.
:::locale "ja"
$`f : X \times Y \to \mathbb{R}` が $`\mu \times \nu` に関して可積分であるとする。
$`\nu` は S-有限であると仮定する。
このとき関数
$$`
  x \longmapsto \int_{y \in Y} f^-(x,y)\,d\nu
`
は $`X` から $`\mathbb{R}` への関数として $`\mu` に関して可積分である。
:::
::::
:::::

```leanDecl
MTI.measurable_integral_section_negPart
MTI.lintegral_integral_section_negPart_ne_top
MTI.integrable_integral_section_negPart
```

:::::lemmaBox
::::localized
Let $`f : X \times Y \to \mathbb{R}` be integrable with respect to $`\mu \times \nu`.
Suppose that $`\nu` is S-finite.
Then for $`\mu`-almost every $`x \in X`,
$$`
  \int_{y \in Y} f(x,y)\,d\nu
    =
  \int_{y \in Y} f^+(x,y)\,d\nu
    -
  \int_{y \in Y} f^-(x,y)\,d\nu.`
:::locale "ja"
$`f : X \times Y \to \mathbb{R}` が $`\mu \times \nu` に関して可積分であるとする。
$`\nu` は S-有限であると仮定する。
このとき $`\mu`-ほとんど至る所の $`x \in X` に対して
$$`
  \int_{y \in Y} f(x,y)\,d\nu
    =
  \int_{y \in Y} f^+(x,y)\,d\nu
    -
  \int_{y \in Y} f^-(x,y)\,d\nu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.integral_sections_eq_integral_posPart_sub_integral_negPart_ae
```

:::::theoremBox "Fubini's Theorem" (ja := "フビニの定理")
::::localized
Let $`f : X \times Y \to \mathbb{R}` be integrable with respect to $`\mu \times \nu`.
Suppose that $`\nu` is S-finite.
Then
$$`
  \int_{(x,y) \in X \times Y} f(x,y)\,d(\mu \times \nu)
    =
  \int_{x \in X}
    \int_{y \in Y} f(x,y)\,d\nu\,d\mu.`
:::locale "ja"
$`f : X \times Y \to \mathbb{R}` が $`\mu \times \nu` に関して可積分であるとする。
$`\nu` は S-有限であると仮定する。
このとき
$$`
  \int_{(x,y) \in X \times Y} f(x,y)\,d(\mu \times \nu)
    =
  \int_{x \in X}
    \int_{y \in Y} f(x,y)\,d\nu\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.integral_prod
```

:::::lemmaBox
::::localized
Let $`f : X \times Y \to \mathbb{R}` be measurable.
Suppose that $`\mu` and $`\nu` are S-finite.
Then
$$`
  \int_{(y,x) \in Y \times X} f(x,y)\,d(\nu \times \mu)
    =
  \int_{(x,y) \in X \times Y} f(x,y)\,d(\mu \times \nu).`
:::locale "ja"
$`f : X \times Y \to \mathbb{R}` を可測とする。
$`\mu` と $`\nu` が S-有限であると仮定する。
このとき
$$`
  \int_{(y,x) \in Y \times X} f(x,y)\,d(\nu \times \mu)
    =
  \int_{(x,y) \in X \times Y} f(x,y)\,d(\mu \times \nu).
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.integral_prod_swap
```

:::::theoremBox "Fubini's Theorem for iterated integrals" (ja := "反復積分に対するフビニの定理")
::::localized
Let $`f : X \times Y \to \mathbb{R}` be integrable with respect to $`\mu \times \nu`.
Suppose that $`\mu` and $`\nu` are S-finite.
Then
$$`
  \int_{x \in X}
    \int_{y \in Y} f(x,y)\,d\nu\,d\mu
    =
  \int_{y \in Y}
    \int_{x \in X} f(x,y)\,d\mu\,d\nu.`
:::locale "ja"
$`f : X \times Y \to \mathbb{R}` が $`\mu \times \nu` に関して可積分であるとする。
$`\mu` と $`\nu` は S-有限であると仮定する。
このとき
$$`
  \int_{x \in X}
    \int_{y \in Y} f(x,y)\,d\nu\,d\mu
    =
  \int_{y \in Y}
    \int_{x \in X} f(x,y)\,d\mu\,d\nu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.integral_prod_swap'
```
