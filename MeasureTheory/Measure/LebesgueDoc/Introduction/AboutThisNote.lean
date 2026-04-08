import MeasureTheory.Measure.LebesgueDoc.Support

open Verso Genre Manual

#doc (Manual) "About this Note" =>

%%%
file := "About-This-Note"
tag := "about-this-note"
%%%

:::lebesgueDocSetup
:::

:::localizedPart (ja := "この資料について")
:::

::::localized
This is a supplementary note for MA3064 at University College Cork in 2026.
It collects the main definitions and theorems covered in the course.
:::locale "ja"
これは UCC の 2026 年の MA3064 の補足資料であり、授業で用いる定義と定理をまとめたものです。
:::
::::

::::localized
The source for this note is available on
[GitHub](https://github.com/yuma-mizuno/measure-theory).
:::locale "ja"
この資料のソースは
[GitHub](https://github.com/yuma-mizuno/measure-theory)
で公開しています。
:::
::::

::::localized
As an experiment, this note is accompanied by proofs written in [Lean](https://lean-lang.org), a proof assistant and
programming language for formal mathematics.
Such tools are likely to become increasingly important in the future of mathematics.
Students are not expected to read these proofs directly.
However, if you would like to see the details of a proof, you might try copying a piece of Lean
code and pasting it into your preferred AI agent with a prompt such as,
"Please translate this into natural language."
:::locale "ja"
試験的に、この資料には [Lean](https://lean-lang.org) で書かれた証明をつけています。
Lean は数学を厳密に記述するための proof assistant 兼 programming language です。
このような道具は今後ますます重要になると考えられています。
ただし、受講生に Lean で書かれた証明をそのまま読むことを求めるものではありません。
ですが、証明の詳細を知りたいときは Lean code をコピーして好きな AI エージェントに
「これを自然言語に翻訳してください」と頼んでみるのがよいと思います。
:::
::::

::::localized
Some definitions are borrowed from [Mathlib](https://github.com/leanprover-community/mathlib4), the mathematical library for Lean.
Even when a concept is first introduced here using a definition given in this note,
it may later be replaced by the corresponding Mathlib definition in order to use a more refined API.
:::locale "ja"
定義の一部は Lean の数学ライブラリである [Mathlib](https://github.com/leanprover-community/mathlib4) から拝借しています。
また、ある節では自前で定義を与えていても、後の節ではより洗練された API を用いるために、対応する Mathlib の定義に置き換えることがあります。
:::
::::
