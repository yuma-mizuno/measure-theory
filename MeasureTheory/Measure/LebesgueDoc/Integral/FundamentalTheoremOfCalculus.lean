import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.FTC"
lebesgue_doc_module MeasureTheory.Lean.FTC
lebesgue_doc_module Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Fundamental Theorem of Calculus" =>

%%%
file := "Fundamental-Theorem-of-Calculus"
tag := "fundamental-theorem-of-calculus"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "微積分学の基本定理")
:::

:::::definitionBox
::::localized
Let $`f : \mathbb{R} \to \mathbb{R}` and let $`a, b \in \mathbb{R}`.
The _interval integral_ of $`f`
from $`a` to $`b` is defined by
$$`
  \int_a^b f (x) \, dx
    \coloneqq
  \begin{cases}
    \displaystyle
    \int_{x \in \mathbb{R}} f (x) \, d(\mu|_{(a, b]}) & \text{if $a \leq b$}, \\[1em]
    \displaystyle
    - \int_{x \in \mathbb{R}} f (x) \, d(\mu|_{(b, a]}) & \text{if $b \leq a$},
  \end{cases}`
when both integrals on the right-hand side are integrable.
:::locale "ja"
$`f : \mathbb{R} \to \mathbb{R}` と $`a, b \in \mathbb{R}` とする。
$`f` の $`a` から $`b` までの _区間積分_ を
$$`
  \int_a^b f (x) \, dx
    \coloneqq
  \begin{cases}
    \displaystyle
    \int_{x \in \mathbb{R}} f (x) \, d(\mu|_{(a, b]}) & \text{if $a \leq b$}, \\[1em]
    \displaystyle
    - \int_{x \in \mathbb{R}} f (x) \, d(\mu|_{(b, a]}) & \text{if $b \leq a$},
  \end{cases}
`
で定める。ただし右辺の積分はどちらも可積分であるとする。
:::
::::
:::::

```leanDecl
intervalIntegral
intervalIntegral.integral_of_le
intervalIntegral.integral_of_ge
```

:::::theoremBox "Fundamental Theorem of Calculus" (ja := "微積分学の基本定理")
::::localized
Let $`f : \mathbb{R} \to \mathbb{R}` and let $`a, b, x \in \mathbb{R}`.
Suppose that $`f` is measurable.
Suppose that $`x \in [a,b]`.
Suppose that $`f` is continuous within $`[a,b]` at $`x`.
Then we have
$$`
  \frac{d}{dt} \left. \left( \int_x^{t} f(y) \, dy \right)\right|_{t = x} = f(x),`
where the derivative is taken within $`[a,b]`.
:::locale "ja"
$`f : \mathbb{R} \to \mathbb{R}` と $`a, b, x \in \mathbb{R}` とする。
$`f` は可測であり、$`x \in [a,b]` であり、$`f` は $`x` において $`[a,b]` 内で連続であると仮定する。
このとき
$$`
  \frac{d}{dt} \left. \left( \int_x^{t} f(y) \, dy \right)\right|_{t = x} = f(x)
`
が成り立つ。ただし微分は $`[a,b]` 内で考える。
:::
::::
:::::

```leanDecl
MTI.IsIoc
MTI.Tendsto.hasFiniteIntegralWithin_Icc
MTI.Tendsto.integral_sub_linear_isLittleOWithin_Icc
MTI.integral_sub_linear_isLittleO_of_tendstoWithin_Icc
```

::::localized
Combined with the mean value theorem, the theorem yields a formula for computing the integral of a
function that is the derivative of another function.

:::locale "ja"
平均値の定理とあわせると、なにかの導関数になっている関数の積分を計算する公式が得られます。
:::
::::

:::::theoremBox
::::localized
Let $`f, f' : \mathbb{R} \to \mathbb{R}` and let $`a, b \in \mathbb{R}`.
Suppose that $`a \leq b`.
Suppose that $`f'` is measurable.
Suppose that $`f'` is continuous on $`[a,b]`.
Suppose that for any $`x \in [a,b]`, the derivative of $`f` at $`x` is $`f'(x)`.
Then we have
$$`
  \int_a^b f'(x) \, dx = f(b) - f(a).`
:::locale "ja"
$`f, f' : \mathbb{R} \to \mathbb{R}` と $`a, b \in \mathbb{R}` とする。
$`a \leq b`、$`f'` は可測、$`f'` は $`[a,b]` 上で連続であり、任意の $`x \in [a,b]` に対して
$`f` の $`x` における導関数が $`f'(x)` であると仮定する。
このとき
$$`
  \int_a^b f'(x) \, dx = f(b) - f(a).
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.integral_eq_sub_of_hasDerivAt_of_le
```
