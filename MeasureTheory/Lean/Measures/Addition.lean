import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

noncomputable section

open ENNReal Set MeasureTheory

namespace MTI

variable {X : Type*} [MeasurableSpace X]

local infixr:25 " →ₛ " => SimpleFunc

namespace Measure

/-- The sum of two measures, defined on measurable sets by pointwise addition. -/
def add (μ ν : Measure X) : Measure X :=
  Measure.ofMeasurable (fun A _ ↦ μ A + ν A) (by simp) <| by
    intro A hA hAd
    simpa using (show μ (⋃ i, A i) + ν (⋃ i, A i) = ∑' i, (μ (A i) + ν (A i)) by
      rw [measure_iUnion hAd hA, measure_iUnion hAd hA, ENNReal.tsum_add])

@[simp]
theorem add_apply (μ ν : Measure X) {A : Set X} (hA : MeasurableSet A) :
    Measure.add μ ν A = μ A + ν A := by
  rw [Measure.add]
  exact Measure.ofMeasurable_apply _ hA

end Measure

namespace SimpleFunc

theorem lintegral_add_measure (f : X →ₛ ℝ≥0∞) (μ ν : Measure X) :
    f.lintegral (Measure.add μ ν) = f.lintegral μ + f.lintegral ν := by
  rw [SimpleFunc.lintegral, SimpleFunc.lintegral, SimpleFunc.lintegral]
  simp only [Measure.add_apply, f.measurableSet_preimage]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_add]

end SimpleFunc

theorem lintegral_add_measure (f : X → ℝ≥0∞) (μ ν : Measure X) :
    ∫⁻ x, f x ∂(Measure.add μ ν) = ∫⁻ x, f x ∂μ + ∫⁻ x, f x ∂ν := by
  simp_rw [lintegral_def]
  set S := { g : X →ₛ ℝ≥0∞ | g ≤ fun x ↦ f x }
  simp_rw [iSup_subtype']
  have hsum : ∀ g : X →ₛ ℝ≥0∞,
      g.lintegral μ + g.lintegral ν = g.lintegral (Measure.add μ ν) := by
    intro g
    exact (MTI.SimpleFunc.lintegral_add_measure g μ ν).symm
  have hiSup :
      ⨆ g : S, SimpleFunc.lintegral g (Measure.add μ ν) =
        ⨆ g : S, SimpleFunc.lintegral g μ + SimpleFunc.lintegral g ν := by
    exact Eq.symm (iSup_congr fun g ↦ hsum g)
  calc
    ⨆ g : S, SimpleFunc.lintegral g (Measure.add μ ν)
        = ⨆ g : S, SimpleFunc.lintegral g μ + SimpleFunc.lintegral g ν := hiSup
    _ = (⨆ g : S, SimpleFunc.lintegral g μ) + ⨆ g : S, SimpleFunc.lintegral g ν := by
          have hdir : IsDirectedOrder S := by
            constructor
            rintro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩
            refine ⟨⟨g₁ ⊔ g₂, ?_⟩, ?_⟩
            · intro x
              simp only [SimpleFunc.coe_sup, Pi.sup_apply, sup_le_iff]
              exact ⟨hg₁ x, hg₂ x⟩
            · constructor <;> intro x <;> simp
          rw [iSup_add_iSup_of_monotone]
          all_goals
            rintro ⟨g, hg⟩ ⟨g', hg'⟩ hgg'
            simp only [Subtype.mk_le_mk] at hgg'
            exact SimpleFunc.lintegral_mono hgg' le_rfl

end MTI
