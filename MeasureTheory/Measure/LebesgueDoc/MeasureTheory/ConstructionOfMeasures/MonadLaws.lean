import MeasureTheory.Measure.LebesgueDoc.Support

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Lean.Measures.Bind"
lebesgue_doc_module MeasureTheory.Lean.Measures.Bind
open Verso Genre Manual

set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option linter.style.setOption true

#doc (Manual) "Monad Laws" =>

%%%
file := "Monad-Laws"
tag := "measure-monad-laws"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "モナド則")
:::

:::::lemmaBox
::::localized
The map $`\delta : X \to \Measure(X)` sending $`x` to $`\delta_x` is measurable.
:::locale "ja"
$`x` を $`\delta_x` に送る写像 $`\delta : X \to \Measure(X)` は可測である。
:::
::::
:::::

```leanDecl
MTI.Measure.dirac_measurable
```

:::::lemmaBox
::::localized
The assignment $`\mu \mapsto \mathcal{K}_{\nu}(\mu)` is measurable as a map
$`\Measure(X) \to \Measure(Y)`.
:::locale "ja"
対応 $`\mu \mapsto \mathcal{K}_{\nu}(\mu)` は
$`\Measure(X) \to \Measure(Y)` として可測である。
:::
::::
:::::

```leanDecl
MTI.Measure.bind_measurable
```

:::::theoremBox
::::localized
If $`\nu : X \to \Measure(Y)` and $`\lambda : Y \to \Measure(Z)` are measurable, then
$$`
  \mathcal{K}_\lambda \circ \mathcal{K}_\nu =
        \mathcal{K}_{\mathcal{K}_\lambda \circ \nu},
  \qquad
  \mathcal{K}_\nu \circ \delta = \nu,
  \qquad
  \mathcal{K}_{\delta}(\mu) = \mu.`
:::locale "ja"
$`\nu : X \to \Measure(Y)` と $`\lambda : Y \to \Measure(Z)` が可測ならば
$$`
  \mathcal{K}_\lambda \circ \mathcal{K}_\nu =
        \mathcal{K}_{\mathcal{K}_\lambda \circ \nu},
  \qquad
  \mathcal{K}_\nu \circ \delta = \nu,
  \qquad
  \mathcal{K}_{\delta}(\mu) = \mu.
`
が成り立つ。
:::
::::
:::::

::::localized
These three identities are called the monad laws.
:::locale "ja"
この 3 つの等式はモナド則と呼ばれます。
:::
::::

```leanDecl
MTI.Measure.bind_assoc
MTI.Measure.dirac_bind
MTI.Measure.bind_dirac
```
