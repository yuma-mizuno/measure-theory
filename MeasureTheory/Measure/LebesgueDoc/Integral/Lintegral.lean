import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Lintegral"
lebesgue_doc_module MeasureTheory.Lean.Lintegral
lebesgue_doc_module MeasureTheory.Lean.SimpleFunc
open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Integrals of Nonnegative Functions" =>

%%%
file := "Lintegral"
tag := "lintegral"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "非負関数の積分")
:::

:::::lemmaBox
::::localized
Fix an enumeration $`q : \mathbb{N} \to \mathbb{Q}_{\ge 0}` of the nonnegative rational numbers.
For a function $`f : X \to [0,\infty]` and $`n \in \mathbb{N}`, define
$`\approxFun_n f : X \to [0,\infty]` by
$$`
  (\approxFun_n f)(x)
    \coloneqq
  \max_{\substack{0 \le i < n \\ q_i \le f(x)}} q_i.`
Then the following hold:

1. For any $`n`, the function $`\approxFun_n f` is simple.
2. If $`i \le j`, then $`\approxFun_i f \le \approxFun_j f`.
3. If $`f` is measurable, then for any $`x \in X`,
   $`\sup_{n \in \mathbb{N}} (\approxFun_n f)(x) = f(x)`.
:::locale "ja"
非負有理数の列挙 $`q : \mathbb{N} \to \mathbb{Q}_{\ge 0}` を固定する。
関数 $`f : X \to [0,\infty]` と $`n \in \mathbb{N}` に対して、
$`\approxFun_n f : X \to [0,\infty]` を
$$`
  (\approxFun_n f)(x)
    \coloneqq
  \max_{\substack{0 \le i < n \\ q_i \le f(x)}} q_i
`
で定める。このとき次が成り立つ。

1. 任意の $`n` に対して、$`\approxFun_n f` は単関数である。
2. $`i \le j` ならば $`\approxFun_i f \le \approxFun_j f` である。
3. $`f` が可測ならば、任意の $`x \in X` に対して
   $`\sup_{n \in \mathbb{N}} (\approxFun_n f)(x) = f(x)` である。
:::
::::
:::::

```leanDecl
MTI.SimpleFunc.ennrealRatEmbed
MTI.SimpleFunc.eapprox
MTI.SimpleFunc.monotone_eapprox
MTI.SimpleFunc.iSup_eapprox_apply
```

:::::definitionBox
::::localized
Let $`X` be a measurable space, let $`\mu` be a measure on $`X`, and let
$`f : X \to [0,\infty]` be a function.
We define the _lower Lebesgue integral_ of $`f` with respect to $`\mu` by
$$`
  \underline{\int}_{x \in X} f(x)\,d\mu
    \coloneqq
  \sup_{\substack{g : X \to [0,\infty],\\ \text{$g$ is simple},\, g \leq f}}
    \Simp \int_{x \in X} g(x)\,d\mu.`
:::locale "ja"
$`X` を可測空間とし、$`\mu` を $`X` 上の測度、$`f : X \to [0,\infty]` を関数とする。
$`f` の $`\mu` に関する _下ルベーグ積分_ を
$$`
  \underline{\int}_{x \in X} f(x)\,d\mu
    \coloneqq
  \sup_{\substack{g : X \to [0,\infty],\\ \text{$g$ is simple},\, g \leq f}}
    \Simp \int_{x \in X} g(x)\,d\mu
`
で定める。
:::
::::
:::::

```leanDecl
MTI.lintegral
```

:::::lemmaBox
::::localized
Let $`f : X \to [0,\infty]` be a simple function.
Then
$$`
  \underline{\int}_{x \in X} f(x)\,d\mu
    = \Simp \int_{x \in X} f(x)\,d\mu.`
:::locale "ja"
$`f : X \to [0,\infty]` を単関数とする。
このとき
$$`
  \underline{\int}_{x \in X} f(x)\,d\mu
    = \Simp \int_{x \in X} f(x)\,d\mu
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.SimpleFunc.lintegral_eq_lintegral
```

:::::lemmaBox
::::localized
In the definition of the lower Lebesgue integral, it is enough to take simple functions with
values in $`\mathbb{R}_{\ge 0}`.
More precisely,
$$`
  \underline{\int}_{x \in X} f(x)\,d\mu
    =
  \sup_{\substack{g : X \to \mathbb{R}_{\ge 0},\\ \text{$g$ is simple},\, g \le f}}
    \Simp \int_{x \in X} g(x)\,d\mu.`
:::locale "ja"
下ルベーグ積分の定義では、値が $`\mathbb{R}_{\ge 0}` に入る単関数だけを考えれば十分である。
より正確には、
$$`
  \underline{\int}_{x \in X} f(x)\,d\mu
    =
  \sup_{\substack{g : X \to \mathbb{R}_{\ge 0},\\ \text{$g$ is simple},\, g \le f}}
    \Simp \int_{x \in X} g(x)\,d\mu
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.lintegral_eq_nnreal
```

:::::theoremBox "Monotone Convergence Theorem" (ja := "単調収束定理")
::::localized
Let $`f_0, f_1, \dots : X \to [0,\infty]` be a sequence of measurable functions.
Suppose that $`f_n \le f_m` whenever $`n \le m`.
Then
$$`
  \underline{\int}_{x \in X} \sup_{n \in \mathbb{N}} f_n(x)\,d\mu
    =
  \sup_{n \in \mathbb{N}} \underline{\int}_{x \in X} f_n(x)\,d\mu.`
:::locale "ja"
$`f_0, f_1, \dots : X \to [0,\infty]` を可測関数の列とする。
$`n \le m` ならば $`f_n \le f_m` であると仮定する。
このとき
$$`
  \underline{\int}_{x \in X} \sup_{n \in \mathbb{N}} f_n(x)\,d\mu
    =
  \sup_{n \in \mathbb{N}} \underline{\int}_{x \in X} f_n(x)\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.iSup_lintegral_le
MTI.lintegral_iSup
```

:::::theoremBox
::::localized
Let $`f, g : X \to [0,\infty]` be measurable functions.
Then
$$`
  \underline{\int}_{x \in X} (f(x) + g(x))\,d\mu
    =
  \underline{\int}_{x \in X} f(x)\,d\mu
    +
  \underline{\int}_{x \in X} g(x)\,d\mu.`
:::locale "ja"
$`f, g : X \to [0,\infty]` を可測関数とする。
このとき
$$`
  \underline{\int}_{x \in X} (f(x) + g(x))\,d\mu
    =
  \underline{\int}_{x \in X} f(x)\,d\mu
    +
  \underline{\int}_{x \in X} g(x)\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.lintegral_add
```

:::::theoremBox
::::localized
Let $`f, g : X \to [0,\infty]` be measurable functions.
If $`g \le f` and
$$`
  \underline{\int}_{x \in X} g(x)\,d\mu < \infty,`
then
$$`
  \underline{\int}_{x \in X} (f(x)-g(x))\,d\mu
    =
  \underline{\int}_{x \in X} f(x)\,d\mu
    -
  \underline{\int}_{x \in X} g(x)\,d\mu.`
:::locale "ja"
$`f, g : X \to [0,\infty]` を可測関数とする。
$`g \le f` かつ
$$`
  \underline{\int}_{x \in X} g(x)\,d\mu < \infty
`
と仮定する。
このとき
$$`
  \underline{\int}_{x \in X} (f(x)-g(x))\,d\mu
    =
  \underline{\int}_{x \in X} f(x)\,d\mu
    -
  \underline{\int}_{x \in X} g(x)\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.lintegral_sub
```

:::::theoremBox "Monotone Convergence Theorem (Decreasing Version)" (ja := "単調収束定理（減少列版）")
::::localized
Let $`f_0, f_1, \dots : X \to [0,\infty]` be a decreasing sequence of measurable functions.
If
$$`
  \underline{\int}_{x \in X} f_0(x)\,d\mu < \infty,`
then
$$`
  \underline{\int}_{x \in X} \inf_{n \in \mathbb{N}} f_n(x)\,d\mu
    =
  \inf_{n \in \mathbb{N}} \underline{\int}_{x \in X} f_n(x)\,d\mu.`
:::locale "ja"
$`f_0, f_1, \dots : X \to [0,\infty]` を可測関数の減少列とする。
もし
$$`
  \underline{\int}_{x \in X} f_0(x)\,d\mu < \infty
`
ならば
$$`
  \underline{\int}_{x \in X} \inf_{n \in \mathbb{N}} f_n(x)\,d\mu
    =
  \inf_{n \in \mathbb{N}} \underline{\int}_{x \in X} f_n(x)\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.le_iInf_lintegral
MTI.lintegral_iInf
```

:::::theoremBox "Fatou's Lemma" (ja := "ファトゥの補題")
::::localized
Let $`f_0, f_1, \dots : X \to [0,\infty]` be a sequence of measurable functions.
Then
$$`
  \underline{\int}_{x \in X} \liminf_{n \to \infty} f_n(x)\,d\mu
    \le
  \liminf_{n \to \infty} \underline{\int}_{x \in X} f_n(x)\,d\mu.`
:::locale "ja"
$`f_0, f_1, \dots : X \to [0,\infty]` を可測関数の列とする。
このとき
$$`
  \underline{\int}_{x \in X} \liminf_{n \to \infty} f_n(x)\,d\mu
    \le
  \liminf_{n \to \infty} \underline{\int}_{x \in X} f_n(x)\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.lintegral_liminf_le
```

:::::theoremBox
::::localized
Let $`f_0, f_1, \dots : X \to [0,\infty]` be measurable functions, and let
$`g : X \to [0,\infty]` satisfy $`f_n \le g` for all $`n`.
If
$$`
  \underline{\int}_{x \in X} g(x)\,d\mu < \infty,`
then
$$`
  \limsup_{n \to \infty} \underline{\int}_{x \in X} f_n(x)\,d\mu
    \le
  \underline{\int}_{x \in X} \limsup_{n \to \infty} f_n(x)\,d\mu.`
:::locale "ja"
$`f_0, f_1, \dots : X \to [0,\infty]` を可測関数とし、
$`g : X \to [0,\infty]` が全ての $`n` に対して $`f_n \le g` を満たすとする。
さらに
$$`
  \underline{\int}_{x \in X} g(x)\,d\mu < \infty
`
と仮定する。
このとき
$$`
  \limsup_{n \to \infty} \underline{\int}_{x \in X} f_n(x)\,d\mu
    \le
  \underline{\int}_{x \in X} \limsup_{n \to \infty} f_n(x)\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.limsup_lintegral_le
```

:::::theoremBox "Dominated Convergence Theorem" (ja := "優収束定理")
::::localized
Let $`f_0, f_1, \dots : X \to [0,\infty]` be a sequence of measurable functions,
let $`F : X \to [0,\infty]` be a function, and let $`g : X \to [0,\infty]`.
Suppose that the following conditions hold:

1. For any $`n` and for any $`x \in X`, we have $`f_n(x) \le g(x)`.
2. $`\underline{\int}_{x \in X} g(x)\,d\mu < \infty`.
3. For any $`x \in X`, the sequence $`f_0(x), f_1(x), \dots` converges to $`F(x)`.

Then
$$`
  \lim_{n \to \infty} \underline{\int}_{x \in X} f_n(x)\,d\mu
    =
  \underline{\int}_{x \in X} F(x)\,d\mu.`
:::locale "ja"
$`f_0, f_1, \dots : X \to [0,\infty]` を可測関数の列とし、
$`F : X \to [0,\infty]` を関数、$`g : X \to [0,\infty]` を関数とする。
次を仮定する。

1. 任意の $`n` と任意の $`x \in X` に対して $`f_n(x) \le g(x)` である。
2. $`\underline{\int}_{x \in X} g(x)\,d\mu < \infty` である。
3. 任意の $`x \in X` に対して、列 $`f_0(x), f_1(x), \dots` は $`F(x)` に収束する。

このとき
$$`
  \lim_{n \to \infty} \underline{\int}_{x \in X} f_n(x)\,d\mu
    =
  \underline{\int}_{x \in X} F(x)\,d\mu.
`
が成り立つ。
:::
::::
:::::

```leanDecl
MTI.tendsto_lintegral_of_dominated_convergence
```
