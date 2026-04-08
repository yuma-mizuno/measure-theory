import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

noncomputable section

open ENNReal Set MeasureTheory

namespace MTI

variable {X : Type*} [MeasurableSpace X]

local infixr:25 " →ₛ " => SimpleFunc

namespace Measure

/-- Restriction of a measure to a measurable set. -/
def restrict (μ : Measure X) (A : Set X) (hA : MeasurableSet A) : Measure X :=
  Measure.ofMeasurable (fun B _ ↦ μ (A ∩ B)) (by simp) <| by
    intro B hB hBd
    dsimp only
    rw [Set.inter_iUnion]
    refine measure_iUnion ?_ ?_
    · intro i j hij
      exact (hBd hij).mono Set.inter_subset_right Set.inter_subset_right
    · intro i
      exact hA.inter (hB i)

@[simp]
theorem restrict_apply (μ : Measure X) {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    restrict μ A hA B = μ (A ∩ B) := by
  rw [restrict]
  exact Measure.ofMeasurable_apply _ hB

theorem restrict_toOuterMeasure_eq_toOuterMeasure_restrict (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) (B : Set X) :
    Measure.restrict μ A hA B = μ (A ∩ B) := by
  apply le_antisymm
  · rcases μ.exists_measurable_superset_eq_trim (A ∩ B) with ⟨C, hCAB, hC, hμC⟩
    rw [← measure_eq_trim] at hμC
    rw [← hμC]
    rw [inter_comm] at hCAB
    rw [inter_subset] at hCAB
    apply (measure_mono hCAB).trans
    simp only [Measure.coe_toOuterMeasure]
    rw [Measure.restrict_apply _ hA (hA.compl.union hC)]
    apply le_trans (le_of_eq _) (measure_mono (show A ∩ C ⊆ C from Set.inter_subset_right))
    have : A ∩ (Aᶜ ∪ C) = A ∩ C := by grind
    grind
  · conv_rhs => rw [measure_eq_iInf]
    apply le_iInf
    intro C
    apply le_iInf
    intro hBC
    apply le_iInf
    intro hC
    rw [Measure.restrict_apply _ hA hC]
    exact measure_mono (inter_subset_inter_right A hBC)

end Measure

namespace SimpleFunc

open scoped Classical in
theorem restrict_lintegral (f : X →ₛ ℝ≥0∞) {A : Set X} (hA : MeasurableSet A) (μ : Measure X) :
    (f.restrict A).lintegral μ = ∑ r ∈ f.range, r * μ (f ⁻¹' {r} ∩ A) :=
  calc
    (f.restrict A).lintegral μ = ∑ r ∈ f.range, r * μ (f.restrict A ⁻¹' {r}) := by
      exact SimpleFunc.lintegral_eq_of_subset _ fun x hx => by
        by_cases hxA : x ∈ A
        · simp [f.restrict_apply hA, hxA]
        · exfalso
          exact hx <| by simp [SimpleFunc.restrict, hA, hxA]
    _ = ∑ r ∈ f.range, r * μ (f ⁻¹' {r} ∩ A) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      by_cases hb0 : b = 0
      · simp [hb0, zero_mul]
      · rw [SimpleFunc.restrict_preimage_singleton _ hA hb0, inter_comm]

theorem lintegral_restrict_measure (f : X →ₛ ℝ≥0∞) (μ : Measure X) {A : Set X} :
    ∀ hA : MeasurableSet A,
      f.lintegral (Measure.restrict μ A hA) = ∑ y ∈ f.range, y * μ (f ⁻¹' {y} ∩ A) := by
  intro hA
  rw [SimpleFunc.lintegral]
  simp only [Measure.restrict_apply, f.measurableSet_preimage]
  apply Finset.sum_congr rfl
  intro y hy
  rw [inter_comm]

theorem restrict_lintegral_eq_lintegral_restrict_measure (f : X →ₛ ℝ≥0∞) {A : Set X}
    (hA : MeasurableSet A) (μ : Measure X) :
    (f.restrict A).lintegral μ = f.lintegral (Measure.restrict μ A hA) := by
  rw [SimpleFunc.restrict_lintegral f hA μ, SimpleFunc.lintegral_restrict_measure f μ hA]

end SimpleFunc

theorem lintegral_indicator_le (f : X → ℝ≥0∞) (A : Set X) (μ : Measure X)
    (hA : MeasurableSet A) :
    ∫⁻ x, A.indicator f x ∂μ ≤ ∫⁻ x, f x ∂(Measure.restrict μ A hA) := by
  simp only [lintegral]
  apply iSup_le fun g ↦ iSup_le fun hg ↦ ?_
  have hgf : g ≤ f := hg.trans (indicator_le_self A f)
  refine le_iSup_of_le g <| le_iSup_of_le hgf <| le_of_eq ?_
  rw [SimpleFunc.lintegral_restrict_measure g μ hA, SimpleFunc.lintegral]
  congr with t
  by_cases ht : t = 0
  · simp [ht]
  · congr with x
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, iff_self_and]
    rintro rfl
    contrapose! ht
    simpa [ht] using hg x

theorem lintegral_restrict {μ : Measure X} {A : Set X} (hA : MeasurableSet A)
    (f : X → ℝ≥0∞) :
    ∫⁻ x, f x ∂(Measure.restrict μ A hA) = ∫⁻ x, A.indicator f x ∂μ := by
  apply le_antisymm ?_ (lintegral_indicator_le f A μ hA)
  simp only [lintegral, iSup_subtype']
  refine iSup_mono' (Subtype.forall.2 fun g hg ↦ ?_)
  refine ⟨⟨g.restrict A, fun x ↦ ?_⟩, ?_⟩
  · simp [hg x, hA, indicator_le_indicator]
  · exact le_of_eq (MTI.SimpleFunc.restrict_lintegral_eq_lintegral_restrict_measure g hA μ).symm

end MTI
