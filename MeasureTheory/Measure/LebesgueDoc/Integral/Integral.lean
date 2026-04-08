import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Integral"
lebesgue_doc_module MeasureTheory.Lean.Integral
open Verso Genre Manual

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Integrals of Real-Valued Functions" =>

%%%
file := "Integral"
tag := "integral"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "実数値関数の積分")
:::

::::localized
Let $`X` be a measurable space, let $`\mu` be a measure on $`X`, and
let $`f : X \to \mathbb{R}` be a real-valued function.
:::locale "ja"
$`X` を可測空間とし、$`\mu` を $`X` 上の測度、$`f : X \to \mathbb{R}` を実数値関数とします。
:::
::::

:::::definitionBox
::::localized
We say that $`f` is _integrable_ if $`f` is measurable and
$$`
  \underline{\int}_{x \in X} |f(x)|\,d\mu < \infty.`
:::locale "ja"
$`f` が _可積分_ であるとは、$`f` が可測であり、
$$`
  \underline{\int}_{x \in X} |f(x)|\,d\mu < \infty
`
が成り立つことをいう。
:::
::::
:::::

```leanDecl
MTI.HasFiniteIntegral
MTI.Integrable
```

:::::definitionBox
::::localized
We define the _positive part_ and _negative part_ of $`f` by
$$`
  f^+(x) \coloneqq \max(f(x), 0),
  \qquad
  f^-(x) \coloneqq \max(-f(x), 0).`
:::locale "ja"
$`f` の _正部分_ と _負部分_ を
$$`
  f^+(x) \coloneqq \max(f(x), 0),
  \qquad
  f^-(x) \coloneqq \max(-f(x), 0)
`
で定める。
:::
::::
:::::

```leanDecl
MTI.posPart
MTI.negPart
```

:::::lemmaBox
::::localized
If $`f` is integrable, then both signed parts have finite lower integral:
$$`
  \underline{\int}_{x \in X} f^+(x)\,d\mu < \infty,
  \qquad
  \underline{\int}_{x \in X} f^-(x)\,d\mu < \infty.`
:::locale "ja"
$`f` が可積分ならば、正部分と負部分はどちらも有限な下積分をもつ:
$$`
  \underline{\int}_{x \in X} f^+(x)\,d\mu < \infty,
  \qquad
  \underline{\int}_{x \in X} f^-(x)\,d\mu < \infty.
`
:::
::::
:::::

```leanDecl
MTI.Integrable.posPart_ne_top
MTI.Integrable.negPart_ne_top
```

:::::definitionBox
::::localized
For an integrable real-valued function $`f : X \to \mathbb{R}`, we define its _Lebesgue integral_ by
$$`
  \int_{x \in X} f(x)\,d\mu
    \coloneqq
    \underline{\int}_{x \in X} f^+(x)\,d\mu
  -
    \underline{\int}_{x \in X} f^-(x)\,d\mu.`
:::locale "ja"
可積分な実数値関数 $`f : X \to \mathbb{R}` に対して、その _ルベーグ積分_ を
$$`
  \int_{x \in X} f(x)\,d\mu
    \coloneqq
    \underline{\int}_{x \in X} f^+(x)\,d\mu
  -
    \underline{\int}_{x \in X} f^-(x)\,d\mu
`
で定める。
:::
::::
:::::

```leanDecl
MTI.integral
```

:::::lemmaBox
::::localized
The Lebesgue integral is linear on integrable real-valued functions:
$$`
  \int_{x \in X} (f(x) + g(x))\,d\mu
    =
  \int_{x \in X} f(x)\,d\mu
    +
  \int_{x \in X} g(x)\,d\mu.
`
$$`
  \int_{x \in X} c f(x)\,d\mu
    =
  c \int_{x \in X} f(x)\,d\mu.
`
:::locale "ja"
ルベーグ積分は可積分な実数値関数の上で線形である:
$$`
  \int_{x \in X} (f(x) + g(x))\,d\mu
    =
  \int_{x \in X} f(x)\,d\mu
    +
  \int_{x \in X} g(x)\,d\mu.
`
$$`
  \int_{x \in X} c f(x)\,d\mu
    =
  c \int_{x \in X} f(x)\,d\mu.
`
:::
::::
:::::

```leanDecl
MTI.integral_add_eq_integral_add
MTI.integral_const_mul
```

:::::lemmaBox
::::localized
The integral of the absolute value bounds the absolute value of the integral:
$$`
  \left|\int_{x \in X} f(x)\,d\mu\right|
    \le
  \int_{x \in X} |f(x)|\,d\mu.`
:::locale "ja"
絶対値の積分は積分の絶対値を上から抑える:
$$`
  \left|\int_{x \in X} f(x)\,d\mu\right|
    \le
  \int_{x \in X} |f(x)|\,d\mu.
`
:::
::::
:::::

```leanDecl
MTI.abs_integral_le_integral_abs
```

:::::theoremBox "Dominated Convergence Theorem" (ja := "優収束定理")
::::localized
Let $`F_0, F_1, \dots : X \to \mathbb{R}` be measurable functions, and let
$`g : X \to \mathbb{R}` be integrable.
Suppose that
$$`
  |F_n(x)| \le g(x)`
for any $`n \in \mathbb{N}` and any $`x \in X`.
Suppose also that
$$`
  F_n(x) \to f(x)`
for any $`x \in X`.
Then
$$`
  \lim_{n \to \infty} \int_{x \in X} F_n(x)\,d\mu
    =
  \int_{x \in X} f(x)\,d\mu.`
:::locale "ja"
$`F_0, F_1, \dots : X \to \mathbb{R}` を可測関数の列とし、
$`g : X \to \mathbb{R}` を可積分関数とする。
さらに任意の $`n \in \mathbb{N}` と任意の $`x \in X` に対して
$$`
  |F_n(x)| \le g(x)
`
が成り立ち、任意の $`x \in X` に対して
$$`
  F_n(x) \to f(x)
`
が成り立つとする。
このとき
$$`
  \lim_{n \to \infty} \int_{x \in X} F_n(x)\,d\mu
    =
  \int_{x \in X} f(x)\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.tendsto_integral_of_dominated_convergence
```
