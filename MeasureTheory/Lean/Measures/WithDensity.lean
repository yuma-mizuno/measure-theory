import Mathlib.MeasureTheory.Integral.Lebesgue.Add

noncomputable section

open ENNReal Set MeasureTheory

namespace MTI

variable {X : Type*} [MeasurableSpace X]

namespace Measure

/-- The measure with density `f` with respect to `μ`. -/
def withDensity (μ : Measure X) (f : X → ℝ≥0∞) : Measure X :=
  Measure.ofMeasurable (fun A _ ↦ ∫⁻ x in A, f x ∂μ) (by simp) <| by
    intro A hA hAd
    exact lintegral_iUnion hA hAd f

theorem withDensity_apply (μ : Measure X) (f : X → ℝ≥0∞) {A : Set X}
    (hA : MeasurableSet A) :
    Measure.withDensity μ f A = ∫⁻ x in A, f x ∂μ := by
  rw [Measure.withDensity]
  exact Measure.ofMeasurable_apply _ hA

end Measure

theorem lintegral_withDensity_eq_lintegral_mul (μ : Measure X) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, g x ∂(Measure.withDensity μ f) = ∫⁻ x, (f * g) x ∂μ := by
  have lhs := calc
    ∫⁻ x, g x ∂(Measure.withDensity μ f) =
      ∫⁻ x : X, ⨆ i, (SimpleFunc.eapprox g i) x ∂(Measure.withDensity μ f) := by
        apply lintegral_congr
        intro x
        exact (SimpleFunc.iSup_eapprox_apply hg x).symm
    _ = ⨆ n, ∫⁻ x : X, (SimpleFunc.eapprox g n) x ∂(Measure.withDensity μ f) := by
        apply lintegral_iSup
        · intro n
          exact (SimpleFunc.eapprox g n).measurable
        · exact SimpleFunc.monotone_eapprox g
  have rhs := calc
    ∫⁻ x, (f * g) x ∂μ =
      ∫⁻ x : X, ⨆ i, f x * (SimpleFunc.eapprox g i) x ∂μ := by
        apply lintegral_congr
        intro x
        simp only [Pi.mul_apply, ← mul_iSup]
        exact congrArg (fun t => f x * t) (SimpleFunc.iSup_eapprox_apply hg x).symm
    _ = ⨆ n, ∫⁻ x : X, f x * (SimpleFunc.eapprox g n) x ∂μ := by
        apply lintegral_iSup
        · intro n
          exact hf.mul (SimpleFunc.eapprox g n).measurable
        · apply monotone_lam
          intro x
          exact Monotone.const_mul' (fun a b hab => SimpleFunc.monotone_eapprox g hab x) (f x)
  rw [lhs, rhs]
  apply iSup_congr
  intro n
  calc
    ∫⁻ x : X, (SimpleFunc.eapprox g n) x ∂(Measure.withDensity μ f)
        = ∑ y ∈ (SimpleFunc.eapprox g n).range,
            ∫⁻ x : X in (SimpleFunc.eapprox g n) ⁻¹' {y}, y * f x ∂μ := by
          rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
          apply Finset.sum_congr rfl
          intro y hy
          rw [Measure.withDensity_apply _ _ ((SimpleFunc.eapprox g n).measurableSet_fiber y)]
          rw [lintegral_const_mul _ hf]
    _ = ∑ y ∈ (SimpleFunc.eapprox g n).range,
          ∫⁻ x : X in (SimpleFunc.eapprox g n) ⁻¹' {y}, (SimpleFunc.eapprox g n) x * f x ∂μ := by
          apply Finset.sum_congr rfl
          intro y hy
          apply setLIntegral_congr_fun ((SimpleFunc.eapprox g n).measurableSet_fiber y)
          intro x hx
          simp only [mem_preimage, mem_singleton_iff] at hx
          simp [hx]
    _ = ∫⁻ x : X, f x * (SimpleFunc.eapprox g n) x ∂μ := by
          rw [← lintegral_finset_sum_measure]
          apply congrArg₂
          · ext A hA
            simp only [Measure.coe_finset_sum, Finset.sum_apply]
            simp only [Measure.restrict_apply hA]
            rw [← measure_biUnion_finset]
            · apply congrArg
              ext x
              simp only [← inter_iUnion]
              rw [mem_inter_iff]
              simp
            · have hpair :
                  ((SimpleFunc.eapprox g n).range : Set ℝ≥0∞).PairwiseDisjoint
                    fun y ↦ (SimpleFunc.eapprox g n) ⁻¹' {y} := by
                exact pairwiseDisjoint_fiber (SimpleFunc.eapprox g n) (SimpleFunc.eapprox g n).range
              intro y hy z hz hyz s hy' hz'
              simp only [le_eq_subset, subset_inter_iff] at hy' hz'
              exact hpair hy hz hyz hy'.2 hz'.2
            · intro y hy
              exact hA.inter ((SimpleFunc.eapprox g n).measurableSet_fiber y)
          · ext x
            ring

end MTI
