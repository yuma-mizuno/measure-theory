import MeasureTheory.Measure.LebesgueDoc.Introduction.AboutThisNote
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.MeasurableSpaces
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.Measure
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.OuterMeasure
import MeasureTheory.Measure.LebesgueDoc.MeasureOnR.OuterMeasure
import MeasureTheory.Measure.LebesgueDoc.MeasureOnR.MeasurableSets
import MeasureTheory.Measure.LebesgueDoc.MeasureOnR.CaratheodoryCriterion
import MeasureTheory.Measure.LebesgueDoc.MeasureOnR.CountableAdditivity
import MeasureTheory.Measure.LebesgueDoc.MeasureOnR.ApproximationByMeasurableSupersets
import MeasureTheory.Measure.LebesgueDoc.MeasureOnR.FailureOfAdditivity
import MeasureTheory.Measure.LebesgueDoc.MeasureOnR.SimpleFunctions
import MeasureTheory.Measure.LebesgueDoc.MeasureOnR.Lintegral
import MeasureTheory.Measure.LebesgueDoc.MeasureOnR.Integral
import MeasureTheory.Measure.LebesgueDoc.Integral.SimpleFunctions
import MeasureTheory.Measure.LebesgueDoc.Integral.Lintegral
import MeasureTheory.Measure.LebesgueDoc.Integral.Integral
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.AE
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Bind
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Addition
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Dirac
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.MonadLaws
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Pushforward
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Restriction
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Sum
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.WithDensity
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.GeneratedBySets
import MeasureTheory.Measure.LebesgueDoc.Integral.FundamentalTheoremOfCalculus
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ProductMeasure
import MeasureTheory.Measure.LebesgueDoc.MeasureTheory.Fubini

set_option verso.exampleProject "."
set_option verso.exampleModule "MeasureTheory.Measure.Lebesgue"
set_option linter.style.emptyLine false
open Verso Genre Manual

#doc (Manual) "Measure Theory and Integration" =>

%%%
authors := ["Yuma Mizuno"]
tag := "measure-theory-and-integration"
%%%

:::localizedPart (ja := "測度論と積分") (jaAuthor := "水野勇磨")
:::

# Introduction
%%%
tag := "introduction"
%%%

:::localizedPart (ja := "はじめに")
:::

{include 2 MeasureTheory.Measure.LebesgueDoc.Introduction.AboutThisNote}

# Measure on ℝ
%%%
file := "Measure-on-R"
tag := "measure-on-r"
%%%

:::localizedPart (ja := "実数直線上の測度")
:::

::::localized
To every subset $`A \subseteq \mathbb{R}` we assign a value $`m(A)` called the *Lebesgue outer
measure*. In the sense that $`m([0,1]) = 1`, it extends the length of an interval and measures the
"size" of a general set of real numbers.

However, it is known that there are two disjoint sets $`A` and $`B` such that
$`m(A \cup B) \neq m(A) + m(B)`. This means that additivity, which is a basic property one would
want from any notion of size, can fail, and this is a problem.

The solution is that we give up asking for additivity on all sets.
Instead, we take the view that it is enough for additivity to hold on the sets obtained
inductively from ordinary sets by ordinary operations.
This is the idea of *measurable sets*. In fact, we prove that additivity does hold on measurable
sets.

We also show that the Lebesgue outer measure behaves well with respect to limiting operations. This
is one of the main reasons why it becomes so useful later in integration theory.
:::locale "ja"
実数の任意の部分集合 $`A` に、*ルベーグ外測度* $`m(A)` という値を割り当てます。これは
$`m([0, 1]) = 1` を満たすという意味で区間の長さの一般化になっており、一般の実数集合の「大きさ」を測っています。

しかし、交わらない二つの集合 $`A` と $`B` について、$`m(A ∪ B) \neq m(A) + m(B)` となりうることが知られています。
これは、「大きさ」という概念に期待したい基本的な性質である加法性が成り立たない場合があることを意味しており、問題になります。

そこで、すべての集合について加法性を要求することはやめます。
その代わりに、普通の集合から普通の操作で帰納的に得られる集合について加法性が成り立てば十分であると考えます。
これが *可測集合* の考え方です。実際、可測集合については加法性が成り立つことを証明します。

また、ルベーグ外測度が極限操作とも相性よく振る舞うことも確かめます。これは、後に積分論でこの概念が非常に有用になる大きな理由の一つです。
:::
::::

{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureOnR.OuterMeasure}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureOnR.MeasurableSets}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureOnR.CaratheodoryCriterion}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureOnR.CountableAdditivity}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureOnR.ApproximationByMeasurableSupersets}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureOnR.FailureOfAdditivity}

# Integration on ℝ
%%%
file := "Integration-on-R"
tag := "integration-on-r"
%%%

:::localizedPart (ja := "実数直線上の積分")
:::

::::localized
We would like to study the integral of a real-valued function $`f : \mathbb{R} \to \mathbb{R}`.
However, for several reasons, it is better to begin with nonnegative functions
$`f : \mathbb{R} \to [0, \infty]` that are allowed to take the value $`\infty`.

One important idea in the Lebesgue integral is to focus on the values taken by a function.
Suppose, for example, that $`f` takes only the values $`\{0,2,3\}`.
How should its integral be defined?
In that case, the integral should be
$$`
  2 \cdot m(f^{-1}\{2\}) + 3 \cdot m(f^{-1}\{3\})
`
that is, the sum over the values in the range, where each value is weighted by the measure of the
set of points on which the function takes that value.
Such a function is called a *simple function*, and its integral is very easy to understand.
To make sense of this quantity, the sets $`f^{-1}\{2\}` and $`f^{-1}\{3\}` must be measurable, but
the important point is that we do not need to know their precise shape.
It is enough to know their measures.
This is what it means to focus on the range rather than on the domain.

Of course, a general function $`f` need not take only finitely many values.
But one can approximate a *measurable function* by a monotonically increasing
sequence of simple functions.
For example, one may enumerate the nonnegative rational numbers as $`q_0, q_1, \dots`, and let the
$`n`th approximation to $`f` be a simple function whose values are among the rational numbers that
appear up to stage $`n`.
Since the rational numbers are dense in the real numbers, this gives a sufficiently good
approximating sequence.

The Lebesgue integral defined in this way satisfies several important convergence theorems.
Here we introduce three of them: the *monotone convergence theorem*,
*Fatou's lemma*, and the *dominated convergence theorem*.
:::locale "ja"
実数値関数 $`f : \mathbb{R} \to \mathbb{R}` の積分を考えたいと思います。
しかし、いくつかの理由から、まずは無限大の値を許す非負関数 $`f : \mathbb{R} \to [0, \infty]` の積分から始めましょう。

ルベーグ積分の重要なアイディアの一つは、値域に注目することです。
たとえば、$`f` が $`\{0, 2, 3\}` の値しか取らないとわかっているとします。そのとき、$`f` の積分はどのように定義されるべきでしょうか。
この場合、$`f` の積分は
$$`
  2 \cdot m(f^{-1}\{2\}) + 3 \cdot m(f^{-1}\{3\})
`
のように、値域の各値に対して、その値を取る点の集合の測度をその値で重み付けして足し合わせたものになるはずです。
このような $`f` は *単関数* と呼ばれ、その積分は非常にわかりやすい形になります。
この値を考えるには $`f^{-1}\{2\}` と $`f^{-1}\{3\}` が可測集合である必要がありますが、重要なのは、それらの集合の正確な形を知る必要はないということです。
測度さえわかれば十分です。これが、定義域よりも値域に着目するということの意味です。

もちろん、一般の $`f` が有限個の値しか取らないとは限りません。しかし、一般の *可測関数* は、そのような単関数の単調増大列で近似できます。
たとえば、非負有理数を $`q_0, q_1, \dots` のように並べ、$`f` の $`n` 番目の近似を、$`n` 番目までに現れた有理数だけを値に持つ単関数として作ることができます。
有理数は実数の中で稠密なので、これは十分によい近似列になります。

このようにして定義されたルベーグ積分は、いくつかの重要な収束定理を満たします。
ここでは、*単調収束定理*、*ファトゥの補題*、*優収束定理* と呼ばれる三つの収束定理を紹介します。
:::
::::

{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureOnR.SimpleFunctions}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureOnR.Lintegral}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureOnR.Integral}

# Measurable Space and Measure
%%%
file := "Measurable-Space-and-Measure"
tag := "measure"
%%%

:::localizedPart (ja := "可測空間と測度")
:::

{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.MeasurableSpaces}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.Measure}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.OuterMeasure}

{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.GeneratedBySets}

# Integral with Respect to a Measure
%%%
tag := "integrals"
%%%

:::localizedPart (ja := "測度に関する積分")
:::

{include 2 MeasureTheory.Measure.LebesgueDoc.Integral.SimpleFunctions}
{include 2 MeasureTheory.Measure.LebesgueDoc.Integral.Lintegral}
{include 2 MeasureTheory.Measure.LebesgueDoc.Integral.Integral}

# Almost Everywhere
%%%
tag := "almost-everywhere"
%%%

:::localizedPart (ja := "ほとんど至る所")
:::

{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.AE}

# Construction of Measures
%%%
tag := "construction-of-measures"
%%%

:::localizedPart (ja := "測度の構成")
:::

{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Restriction}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Pushforward}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Dirac}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Addition}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Sum}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.WithDensity}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.Bind}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ConstructionOfMeasures.MonadLaws}

# Fundamental Theorem of Calculus
%%%
tag := "fundamental-theorem-of-calculus-chapter"
%%%

:::localizedPart (ja := "微積分学の基本定理")
:::

{include 2 MeasureTheory.Measure.LebesgueDoc.Integral.FundamentalTheoremOfCalculus}

# Product Measure and Fubini-Tonelli Theorem
%%%
tag := "product-measure-and-fubini-tonelli-theorem"
%%%

:::localizedPart (ja := "直積測度とフビニ・トネリの定理")
:::

{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.ProductMeasure}
{include 2 MeasureTheory.Measure.LebesgueDoc.MeasureTheory.Fubini}
