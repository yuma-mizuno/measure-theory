import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lebesgue.Integral"
set_option maxHeartbeats 1000000
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.Integral
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.Lintegral

open Verso Genre Manual

#doc (Manual) "Integrals of Real-Valued Functions on ℝ" =>

%%%
file := "Integrals-of-Real-Valued-Functions-on-R"
tag := "integrals-of-real-valued-functions-on-r"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "実数直線上の実数値関数の積分")
:::

::::localized
Let $`f : \mathbb{R} \to \mathbb{R}` be a real-valued function.
:::locale "ja"
$`f : \mathbb{R} \to \mathbb{R}` を実数値関数とします。
:::
::::

:::::definitionBox
::::localized
We say that $`f` is _integrable_ if $`f` is measurable and
$$`
  \underline{\int}_{x \in \mathbb{R}} |f(x)|\,dx < \infty.`
:::locale "ja"
$`f` が _可積分_ であるとは、$`f` が可測であり、
$$`
  \underline{\int}_{x \in \mathbb{R}} |f(x)|\,dx < \infty
`
が成り立つことをいう。
:::
::::
:::::

```leanDecl
MTI.Real.HasFiniteIntegral
MTI.Real.Integrable
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
MTI.Real.posPart
MTI.Real.negPart
```

:::::lemmaBox
::::localized
If $`f` is integrable, then both signed parts have finite lower integral:
$$`
  \underline{\int}_{x \in \mathbb{R}} f^+(x)\,dx < \infty,
  \qquad
  \underline{\int}_{x \in \mathbb{R}} f^-(x)\,dx < \infty.`
:::locale "ja"
$`f` が可積分ならば、正部分と負部分はどちらも有限な下積分をもつ:
$$`
  \underline{\int}_{x \in \mathbb{R}} f^+(x)\,dx < \infty,
  \qquad
  \underline{\int}_{x \in \mathbb{R}} f^-(x)\,dx < \infty.
`
:::
::::
:::::

```leanDecl
MTI.Real.Integrable.posPart_ne_top
MTI.Real.Integrable.negPart_ne_top
```

:::::definitionBox
::::localized
For an integrable real-valued function $`f : \mathbb{R} \to \mathbb{R}`, we define its _Lebesgue integral_ by
$$`
  \int_{x \in \mathbb{R}} f(x)\,dx
    \coloneqq
    \underline{\int}_{x \in \mathbb{R}} f^+(x)\,dx
  -
    \underline{\int}_{x \in \mathbb{R}} f^-(x)\,dx.`
:::locale "ja"
可積分な実数値関数 $`f : \mathbb{R} \to \mathbb{R}` に対して、その _ルベーグ積分_ を
$$`
  \int_{x \in \mathbb{R}} f(x)\,dx
    \coloneqq
    \underline{\int}_{x \in \mathbb{R}} f^+(x)\,dx
  -
    \underline{\int}_{x \in \mathbb{R}} f^-(x)\,dx
`
で定める。
:::
::::
:::::

```leanDecl
MTI.Real.integral
```

:::::lemmaBox
::::localized
If $`f(x) \ge 0` for every $`x`, then the integral agrees with the lower integral:
$$`
  \int_{x \in \mathbb{R}} f(x)\,dx
    =
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx.`
:::locale "ja"
任意の $`x` に対して $`f(x) \ge 0` ならば、積分は下積分と一致する:
$$`
  \int_{x \in \mathbb{R}} f(x)\,dx
    =
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx.
`
:::
::::
:::::

```leanDecl
MTI.Real.integral_eq_lintegral_of_nonneg
MTI.Real.integral_nonneg
MTI.Real.integral_zero
```

:::::lemmaBox
::::localized
The Lebesgue integral is linear on integrable real-valued functions:
$$`
  \begin{aligned}
    \int_{x \in \mathbb{R}} (f(x) + g(x))\,dx
      &=
    \int_{x \in \mathbb{R}} f(x)\,dx \\
      &\quad +
    \int_{x \in \mathbb{R}} g(x)\,dx, \\
    \int_{x \in \mathbb{R}} c f(x)\,dx
      &=
    c \int_{x \in \mathbb{R}} f(x)\,dx.
  \end{aligned}`
:::locale "ja"
ルベーグ積分は可積分な実数値関数の上で線形である:
$$`
  \begin{aligned}
    \int_{x \in \mathbb{R}} (f(x) + g(x))\,dx
      &=
    \int_{x \in \mathbb{R}} f(x)\,dx \\
      &\quad +
    \int_{x \in \mathbb{R}} g(x)\,dx, \\
    \int_{x \in \mathbb{R}} c f(x)\,dx
      &=
    c \int_{x \in \mathbb{R}} f(x)\,dx.
  \end{aligned}
`
:::
::::
:::::

```leanDecl
MTI.Real.integral_add_eq_integral_add
MTI.Real.integral_const_mul
```

:::::lemmaBox
::::localized
The integral of the absolute value bounds the absolute value of the integral:
$$`
  \left|\int_{x \in \mathbb{R}} f(x)\,dx\right|
    \le
  \int_{x \in \mathbb{R}} |f(x)|\,dx.`
:::locale "ja"
絶対値の積分は積分の絶対値を上から抑える:
$$`
  \left|\int_{x \in \mathbb{R}} f(x)\,dx\right|
    \le
  \int_{x \in \mathbb{R}} |f(x)|\,dx.
`
:::
::::
:::::

```leanDecl
MTI.Real.abs_integral_le_lintegral_abs
```

:::::theoremBox "Dominated Convergence Theorem" (ja := "優収束定理")
::::localized
Let $`F_0, F_1, \dots : \mathbb{R} \to \mathbb{R}` be measurable functions, and let
$`g : \mathbb{R} \to \mathbb{R}` be integrable.
Suppose that the following conditions hold:

1. For any $`n \in \mathbb{N}` and any $`x \in \mathbb{R}`, we have $`|F_n(x)| \le g(x)`.
2. For any $`x \in \mathbb{R}`, the sequence $`F_0(x), F_1(x), \dots` converges to $`f(x)`.

Then
$$`
  \lim_{n \to \infty} \int_{x \in \mathbb{R}} F_n(x)\,dx
    =
  \int_{x \in \mathbb{R}} f(x)\,dx.`
:::locale "ja"
$`F_0, F_1, \dots : \mathbb{R} \to \mathbb{R}` を可測関数の列とし、
$`g : \mathbb{R} \to \mathbb{R}` を可積分関数とする。
次を仮定する。

1. 任意の $`n \in \mathbb{N}` と任意の $`x \in \mathbb{R}` に対して $`|F_n(x)| \le g(x)` である。
2. 任意の $`x \in \mathbb{R}` に対して、列 $`F_0(x), F_1(x), \dots` は $`f(x)` に収束する。

このとき
$$`
  \lim_{n \to \infty} \int_{x \in \mathbb{R}} F_n(x)\,dx
    =
  \int_{x \in \mathbb{R}} f(x)\,dx.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.tendsto_integral_of_dominated_convergence
```
