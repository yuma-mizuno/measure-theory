import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import MeasureTheory.Lean.Measures.Addition

noncomputable section

open ENNReal Set MeasureTheory

namespace MTI

variable {X ι : Type*} [MeasurableSpace X]

local infixr:25 " →ₛ " => SimpleFunc

namespace Measure

/-- The sum of an indexed family of measures. -/
def sum (μ : ι → Measure X) : Measure X :=
  Measure.ofMeasurable (fun A _ ↦ ∑' i, μ i A) (by simp) <| by
    intro A hA hAd
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro i
    rw [measure_iUnion hAd hA]

@[simp]
theorem sum_apply (μ : ι → Measure X) {A : Set X} (hA : MeasurableSet A) :
    Measure.sum μ A = ∑' i, μ i A := by
  rw [Measure.sum]
  exact Measure.ofMeasurable_apply _ hA

end Measure

namespace SimpleFunc

theorem lintegral_sum_measure (f : X →ₛ ℝ≥0∞) (μ : ι → Measure X) :
    f.lintegral (Measure.sum μ) = ∑' i, f.lintegral (μ i) := by
  rw [SimpleFunc.lintegral]
  simp_rw [Measure.sum_apply _ (SimpleFunc.measurableSet_fiber f _)]
  simp_rw [← ENNReal.tsum_mul_left]
  refine Eq.symm (Summable.tsum_finsetSum ?_)
  intro y hy
  simp only [ENNReal.summable]

end SimpleFunc

set_option linter.unusedDecidableInType false in
theorem finset_sum_insert_eq_add {I : Type*} [DecidableEq I]
    (i : I) (J : Finset I) (hi : i ∉ J) (μ : I → Measure X) :
    ∑ j ∈ insert i J, μ j = Measure.add (μ i) (∑ j ∈ J, μ j) := by
  ext A hA
  rw [Finset.sum_insert hi]
  rw [MeasureTheory.Measure.add_apply]
  simp only [Measure.add_apply, hA, Measure.coe_finset_sum, Finset.sum_apply]

set_option linter.unusedDecidableInType false in
theorem lintegral_finset_sum_measure {I : Type*} [DecidableEq I]
    (J : Finset I) (f : X → ℝ≥0∞) (μ : I → Measure X) :
    ∫⁻ x, f x ∂∑ i ∈ J, μ i = ∑ i ∈ J, ∫⁻ x, f x ∂μ i := by
  induction J using Finset.induction with
  | empty => simp
  | insert i J hi ih =>
      rw [finset_sum_insert_eq_add i J hi μ]
      rw [MTI.lintegral_add_measure]
      rw [ih]
      rw [Finset.sum_insert hi]

set_option linter.unusedDecidableInType false in
theorem SimpleFunc.lintegral_finset_sum {I : Type*} [DecidableEq I] (J : Finset I)
    (f : X →ₛ ℝ≥0∞) (μ : I → Measure X) :
    f.lintegral (∑ i ∈ J, μ i) = ∑ i ∈ J, f.lintegral (μ i) := by
  induction J using Finset.induction with
  | empty => simp
  | insert i J hi ih =>
      rw [finset_sum_insert_eq_add i J hi μ]
      rw [MTI.SimpleFunc.lintegral_add_measure]
      rw [ih]
      rw [Finset.sum_insert hi]

theorem lintegral_sum_measure (f : X → ℝ≥0∞) (μ : ι → Measure X) :
    ∫⁻ x, f x ∂(Measure.sum μ) = ∑' i, ∫⁻ x, f x ∂μ i := by
  rw [@ENNReal.tsum_eq_iSup_sum]
  classical
  simp_rw [← lintegral_finset_sum_measure, lintegral]
  conv_rhs => rw [iSup_comm]
  conv_rhs =>
    congr
    ext g
    rw [iSup_comm]
  apply iSup_congr
  intro g
  apply iSup_congr
  intro hg
  simp_rw [MTI.SimpleFunc.lintegral_finset_sum]
  rw [@MTI.SimpleFunc.lintegral_sum_measure]
  rw [@ENNReal.tsum_eq_iSup_sum]

end MTI
