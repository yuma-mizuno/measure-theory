import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lebesgue.Lintegral"
set_option maxHeartbeats 1000000
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.Lintegral
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.Measurable
lebesgue_doc_module MeasureTheory.Lean.Lebesgue.SimpleFunc

open Verso Genre Manual

#doc (Manual) "Integrals of Nonnegative Functions on ℝ" =>

%%%
file := "Integrals-of-Nonnegative-Functions-on-R"
tag := "integrals-of-nonnegative-functions-on-r"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "実数直線上の非負関数の積分")
:::

:::::definitionBox
::::localized
Let $`f : \mathbb{R} \to [0,\infty]` be a function.
We say that $`f` is _measurable_ if for any $`a \in [0,\infty]`, the set
$$`
  \{x \in \mathbb{R} \mid a \le f(x)\}`
is measurable.
:::locale "ja"
$`f : \mathbb{R} \to [0,\infty]` を関数とする。
$`f` が _可測_ であるとは、任意の $`a \in [0,\infty]` に対して
$$`
  \{x \in \mathbb{R} \mid a \le f(x)\}
`
が可測であることをいう。
:::
::::
:::::

```leanDecl
MTI.Real.Measurable
```

:::::lemmaBox
::::localized
Fix an enumeration $`q : \mathbb{N} \to \mathbb{Q}_{\ge 0}` of the nonnegative rational numbers.
For a function $`f : \mathbb{R} \to [0,\infty]` and $`n \in \mathbb{N}`, define
$`\approxFun_n f : \mathbb{R} \to [0,\infty]` by
$$`
  (\approxFun_n f)(x)
    \coloneqq
  \max_{\substack{0 \le i < n \\ q_i \le f(x)}} q_i.`
Then the following hold:

1. For any $`n`, the function $`\approxFun_n f` is simple.
2. If $`i \le j`, then $`\approxFun_i f \le \approxFun_j f`.
3. If $`f` is measurable, then for any $`x \in \mathbb{R}`,
   $`\sup_{n \in \mathbb{N}} (\approxFun_n f)(x) = f(x)`.
:::locale "ja"
非負有理数の列挙 $`q : \mathbb{N} \to \mathbb{Q}_{\ge 0}` を固定する。
関数 $`f : \mathbb{R} \to [0,\infty]` と $`n \in \mathbb{N}` に対して、
$`\approxFun_n f : \mathbb{R} \to [0,\infty]` を
$$`
  (\approxFun_n f)(x)
    \coloneqq
  \max_{\substack{0 \le i < n \\ q_i \le f(x)}} q_i
`
で定める。このとき次が成り立つ。

1. 任意の $`n` に対して、$`\approxFun_n f` は単関数である。
2. $`i \le j` ならば $`\approxFun_i f \le \approxFun_j f` である。
3. $`f` が可測ならば、任意の $`x \in \mathbb{R}` に対して
   $`\sup_{n \in \mathbb{N}} (\approxFun_n f)(x) = f(x)` である。
:::
::::
:::::

```leanDecl
MTI.Real.SimpleFunc.ennrealRatEmbed
MTI.Real.SimpleFunc.eapprox
MTI.Real.SimpleFunc.monotone_eapprox
MTI.Real.SimpleFunc.iSup_eapprox_apply
```

:::::definitionBox
::::localized
Let $`f : \mathbb{R} \to [0,\infty]` be a function.
We define the _lower Lebesgue integral_ of $`f` by
$$`
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    \coloneqq
  \sup_{\substack{g : \mathbb{R} \to [0,\infty],\\ \text{$g$ is simple},\, g \le f}}
    \Simp \int_{x \in \mathbb{R}} g(x)\,dx.`
:::locale "ja"
$`f : \mathbb{R} \to [0,\infty]` を関数とする。
$`f` の _下ルベーグ積分_ を
$$`
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    \coloneqq
  \sup_{\substack{g : \mathbb{R} \to [0,\infty],\\ \text{$g$ is simple},\, g \le f}}
    \Simp \int_{x \in \mathbb{R}} g(x)\,dx
`
で定める。
:::
::::
:::::

```leanDecl
MTI.Real.lintegral
```

:::::lemmaBox
::::localized
Let $`f : \mathbb{R} \to [0,\infty]` be a simple function.
Then
$$`
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    = \Simp \int_{x \in \mathbb{R}} f(x)\,dx.`
:::locale "ja"
$`f : \mathbb{R} \to [0,\infty]` を単関数とする。
このとき
$$`
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    = \Simp \int_{x \in \mathbb{R}} f(x)\,dx
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.lintegral_eq_lintegral
```

:::::lemmaBox
::::localized
In the definition of the lower Lebesgue integral, it is enough to take simple functions with
values in $`\mathbb{R}_{\ge 0}`.
More precisely,
$$`
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    =
  \sup_{\substack{g : \mathbb{R} \to \mathbb{R}_{\ge 0},\\ \text{$g$ is simple},\, g \le f}}
    \Simp \int_{x \in \mathbb{R}} g(x)\,dx.`
:::locale "ja"
下ルベーグ積分の定義では、値が $`\mathbb{R}_{\ge 0}` に入る単関数だけを考えれば十分である。
より正確には、
$$`
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    =
  \sup_{\substack{g : \mathbb{R} \to \mathbb{R}_{\ge 0},\\ \text{$g$ is simple},\, g \le f}}
    \Simp \int_{x \in \mathbb{R}} g(x)\,dx
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.lintegral_eq_nnreal
```

:::::theoremBox "Monotone Convergence Theorem" (ja := "単調収束定理")
::::localized
Let $`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` be a sequence of measurable functions.
Suppose that $`f_n \le f_m` whenever $`n \le m`.
Then
$$`
  \underline{\int}_{x \in \mathbb{R}} \sup_{n \in \mathbb{N}} f_n(x)\,dx
    =
  \sup_{n \in \mathbb{N}} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx.`
:::locale "ja"
$`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` を可測関数の列とする。
$`n \le m` ならば $`f_n \le f_m` であると仮定する。
このとき
$$`
  \underline{\int}_{x \in \mathbb{R}} \sup_{n \in \mathbb{N}} f_n(x)\,dx
    =
  \sup_{n \in \mathbb{N}} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.iSup_lintegral_le
MTI.Real.lintegral_iSup
```

:::::theoremBox
::::localized
Let $`f, g : \mathbb{R} \to [0,\infty]` be measurable functions.
Then
$$`
  \underline{\int}_{x \in \mathbb{R}} (f(x) + g(x))\,dx
    =
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    +
  \underline{\int}_{x \in \mathbb{R}} g(x)\,dx.`
:::locale "ja"
$`f, g : \mathbb{R} \to [0,\infty]` を可測関数とする。
このとき
$$`
  \underline{\int}_{x \in \mathbb{R}} (f(x) + g(x))\,dx
    =
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    +
  \underline{\int}_{x \in \mathbb{R}} g(x)\,dx.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.lintegral_add
```

:::::theoremBox
::::localized
Let $`f, g : \mathbb{R} \to [0,\infty]` be measurable functions.
If $`g \le f` and
$$`
  \underline{\int}_{x \in \mathbb{R}} g(x)\,dx < \infty,`
then
$$`
  \underline{\int}_{x \in \mathbb{R}} (f(x)-g(x))\,dx
    =
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    -
  \underline{\int}_{x \in \mathbb{R}} g(x)\,dx.`
:::locale "ja"
$`f, g : \mathbb{R} \to [0,\infty]` を可測関数とする。
$`g \le f` かつ
$$`
  \underline{\int}_{x \in \mathbb{R}} g(x)\,dx < \infty
`
と仮定する。
このとき
$$`
  \underline{\int}_{x \in \mathbb{R}} (f(x)-g(x))\,dx
    =
  \underline{\int}_{x \in \mathbb{R}} f(x)\,dx
    -
  \underline{\int}_{x \in \mathbb{R}} g(x)\,dx.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.lintegral_sub
```

:::::theoremBox "Monotone Convergence Theorem (Decreasing Version)" (ja := "単調収束定理（減少列版）")
::::localized
Let $`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` be a decreasing sequence of measurable
functions.
$$`
  \underline{\int}_{x \in \mathbb{R}} \inf_{n \in \mathbb{N}} f_n(x)\,dx
    \le
  \inf_{n \in \mathbb{N}} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx.`
If
$$`
  \underline{\int}_{x \in \mathbb{R}} f_0(x)\,dx < \infty,`
then
$$`
  \underline{\int}_{x \in \mathbb{R}} \inf_{n \in \mathbb{N}} f_n(x)\,dx
    =
  \inf_{n \in \mathbb{N}} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx.`
:::locale "ja"
$`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` を可測関数の減少列とする。
このとき
$$`
  \underline{\int}_{x \in \mathbb{R}} \inf_{n \in \mathbb{N}} f_n(x)\,dx
    \le
  \inf_{n \in \mathbb{N}} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx.
`
が成り立つ。
さらに
$$`
  \underline{\int}_{x \in \mathbb{R}} f_0(x)\,dx < \infty
`
ならば
$$`
  \underline{\int}_{x \in \mathbb{R}} \inf_{n \in \mathbb{N}} f_n(x)\,dx
    =
  \inf_{n \in \mathbb{N}} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.le_iInf_lintegral
MTI.Real.lintegral_iInf
```

:::::theoremBox "Fatou's Lemma" (ja := "ファトゥの補題")
::::localized
Let $`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` be a sequence of measurable functions.
Then
$$`
  \underline{\int}_{x \in \mathbb{R}} \liminf_{n \to \infty} f_n(x)\,dx
    \le
  \liminf_{n \to \infty} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx.`
:::locale "ja"
$`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` を可測関数の列とする。
このとき
$$`
  \underline{\int}_{x \in \mathbb{R}} \liminf_{n \to \infty} f_n(x)\,dx
    \le
  \liminf_{n \to \infty} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.lintegral_liminf_le
```

:::::theoremBox "Fatou's Lemma (limsup Version)" (ja := "ファトゥの補題（limsup 版）")
::::localized
Let $`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` be measurable functions, and let
$`g : \mathbb{R} \to [0,\infty]` satisfy $`f_n \le g` for all $`n`.
If
$$`
  \underline{\int}_{x \in \mathbb{R}} g(x)\,dx < \infty,`
then
$$`
  \limsup_{n \to \infty} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx
    \le
  \underline{\int}_{x \in \mathbb{R}} \limsup_{n \to \infty} f_n(x)\,dx.`
:::locale "ja"
$`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` を可測関数とし、
$`g : \mathbb{R} \to [0,\infty]` が全ての $`n` に対して $`f_n \le g` を満たすとする。
さらに
$$`
  \underline{\int}_{x \in \mathbb{R}} g(x)\,dx < \infty
`
と仮定する。
このとき
$$`
  \limsup_{n \to \infty} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx
    \le
  \underline{\int}_{x \in \mathbb{R}} \limsup_{n \to \infty} f_n(x)\,dx.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.limsup_lintegral_le
```

:::::theoremBox "Dominated Convergence Theorem" (ja := "優収束定理")
::::localized
Let $`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` be a sequence of measurable functions,
let $`F : \mathbb{R} \to [0,\infty]` be a function, and let $`g : \mathbb{R} \to [0,\infty]`.
Suppose that the following conditions hold:

1. For any $`n` and for any $`x \in \mathbb{R}`, we have $`f_n(x) \le g(x)`.
2. $`\underline{\int}_{x \in \mathbb{R}} g(x)\,dx < \infty`.
3. For any $`x \in \mathbb{R}`, the sequence $`f_0(x), f_1(x), \dots` converges to $`F(x)`.

Then
$$`
  \lim_{n \to \infty} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx
    =
  \underline{\int}_{x \in \mathbb{R}} F(x)\,dx.`
:::locale "ja"
$`f_0, f_1, \dots : \mathbb{R} \to [0,\infty]` を可測関数の列とし、
$`F : \mathbb{R} \to [0,\infty]` を関数、$`g : \mathbb{R} \to [0,\infty]` を関数とする。
次を仮定する。

1. 任意の $`n` と任意の $`x \in \mathbb{R}` に対して $`f_n(x) \le g(x)` である。
2. $`\underline{\int}_{x \in \mathbb{R}} g(x)\,dx < \infty` である。
3. 任意の $`x \in \mathbb{R}` に対して、列 $`f_0(x), f_1(x), \dots` は $`F(x)` に収束する。

このとき
$$`
  \lim_{n \to \infty} \underline{\int}_{x \in \mathbb{R}} f_n(x)\,dx
    =
  \underline{\int}_{x \in \mathbb{R}} F(x)\,dx.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.Real.tendsto_lintegral_of_dominated_convergence
```
