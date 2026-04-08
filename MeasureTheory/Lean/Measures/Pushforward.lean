import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

noncomputable section

open ENNReal Set MeasureTheory

namespace MTI

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

namespace Measure

/-- The pushforward of a measure along a measurable map. -/
def map (f : X → Y) (hf : Measurable f) (μ : Measure X) : Measure Y :=
  Measure.ofMeasurable (fun A _ ↦ μ (f ⁻¹' A)) (by simp) <| by
    intro A hA hAd
    simp only [preimage_iUnion]
    apply measure_iUnion _ (fun i ↦ hf (hA i))
    intro i j hij
    have := hAd hij
    grind

@[simp]
theorem map_apply (f : X → Y) (hf : Measurable f) (μ : Measure X) {A : Set Y}
    (hA : MeasurableSet A) :
    Measure.map f hf μ A = μ (f ⁻¹' A) := by
  rw [Measure.map]
  exact Measure.ofMeasurable_apply _ hA

end Measure

theorem lintegral_map (f : X → Y) (hf : Measurable f)
    (μ : Measure X) {g : Y → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂(Measure.map f hf μ) = ∫⁻ x, g (f x) ∂μ := by
  let h n : SimpleFunc X ℝ≥0∞ := {
    toFun := (SimpleFunc.eapprox g n) ∘ f
    measurableSet_fiber' := fun a ↦ by
      apply (SimpleFunc.measurable (SimpleFunc.eapprox g n)).comp hf
      exact measurableSet_singleton a
    finite_range' := by
      rw [@range_comp]
      have hsubset : (⇑(SimpleFunc.eapprox g n) '' range f) ⊆ range (SimpleFunc.eapprox g n) := by
        exact image_subset_range (⇑(SimpleFunc.eapprox g n)) (range f)
      clear hf hg
      exact Set.Finite.subset (SimpleFunc.finite_range (SimpleFunc.eapprox g n)) hsubset }
  calc
    ∫⁻ y, g y ∂(Measure.map f hf μ) =
        ⨆ n, ∫⁻ y, (SimpleFunc.eapprox g n) y ∂(Measure.map f hf μ) := by
      rw [lintegral_eq_iSup_eapprox_lintegral hg]
      apply iSup_congr
      intro n
      rw [SimpleFunc.lintegral_eq_lintegral]
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * Measure.map f hf μ ((SimpleFunc.eapprox g n) ⁻¹' {a}) := by
      apply iSup_congr
      intro n
      rw [← SimpleFunc.map_lintegral, SimpleFunc.lintegral_eq_lintegral]
      rfl
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * μ (f ⁻¹' ((SimpleFunc.eapprox g n) ⁻¹' {a})) := by
      apply iSup_congr
      intro n
      congr 1 with a
      congr 1
      rw [Measure.map_apply]
      exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox g n) a
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * μ ((SimpleFunc.eapprox g n ∘ f) ⁻¹' {a}) := by
      rfl
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * μ (h n ⁻¹' {a}) := by
      rfl
    _ = ⨆ n, ∑ a ∈ (h n).range, a * μ (h n ⁻¹' {a}) := by
      apply iSup_congr
      intro n
      apply Eq.symm
      apply Finset.sum_subset
      · intro a
        simp only [SimpleFunc.mem_range, mem_range, forall_exists_index]
        intro x hx
        refine ⟨f x, ?_⟩
        rw [← hx]
        rfl
      · intro a
        simp only [SimpleFunc.mem_range, mem_range, not_exists, mul_eq_zero, forall_exists_index]
        intro y hy ha
        right
        have hempty : (h n) ⁻¹' {a} = ∅ := by
          ext x
          simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
          exact ha x
        rw [hempty]
        simp
    _ = ⨆ n, ∫⁻ x, (h n) x ∂μ := by
      apply iSup_congr
      intro n
      rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
    _ = ∫⁻ x, (g ∘ f) x ∂μ := by
      rw [← lintegral_iSup]
      · apply lintegral_congr
        intro x
        simp only [SimpleFunc.coe_mk, Function.comp_apply, h]
        rw [SimpleFunc.iSup_eapprox_apply hg (f x)]
      · intro n
        exact SimpleFunc.measurable (h n)
      · intro i j hij x
        simp only [SimpleFunc.coe_mk, Function.comp_apply, h]
        exact SimpleFunc.monotone_eapprox g hij (f x)

end MTI
