import MeasureTheory.Lean.Lintegral

noncomputable section

open MeasureTheory Set Filter ENNReal

namespace MTI

variable {X : Type*}

theorem preimage_singleton_diff_subset_setOf_ne {α : Type*} (f g : X → α) (y : α) :
    f ⁻¹' {y} \ g ⁻¹' {y} ⊆ {x | f x ≠ g x} := by
  grind

variable [MeasurableSpace X] {μ : Measure X}

theorem measure_congr_of_diff_eq_zero {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : μ (A \ B) = 0) (hBA : μ (B \ A) = 0) :
    μ A = μ B := by
  calc
    μ A = μ ((A \ B) ∪ (A ∩ B)) := by rw [diff_union_inter]
    _ = μ (A \ B) + μ (A ∩ B) := by
      rw [measure_union Set.disjoint_sdiff_inter (hA.inter hB)]
    _ = 0 + μ (A ∩ B) := by rw [hAB]
    _ = μ (B \ A) + μ (B ∩ A) := by rw [hBA, inter_comm]
    _ = μ ((B \ A) ∪ (B ∩ A)) := by
      rw [(measure_union Set.disjoint_sdiff_inter (hB.inter hA)).symm]
    _ = μ B := by rw [diff_union_inter]

theorem SimpleFunc.measure_preimage_singleton_congr_ae (f g : SimpleFunc X)
    (hfg : ∀ᵐ x ∂μ, f x = g x) (y : ℝ≥0∞) :
    μ (f ⁻¹' {y}) = μ (g ⁻¹' {y}) := by
  have hnull : μ {x | f x ≠ g x} = 0 := by
    simpa [ae_iff] using hfg
  have hfg_diff : μ (f ⁻¹' {y} \ g ⁻¹' {y}) = 0 := by
    refine measure_mono_null (preimage_singleton_diff_subset_setOf_ne f g y) hnull
  have hgf_diff : μ (g ⁻¹' {y} \ f ⁻¹' {y}) = 0 := by
    refine measure_mono_null (preimage_singleton_diff_subset_setOf_ne g f y) ?_
    simpa [ne_comm] using hnull
  exact measure_congr_of_diff_eq_zero
    (f.measurableSet_fiber y) (g.measurableSet_fiber y) hfg_diff hgf_diff

theorem lintegral_mono_ae {f g : X → ℝ≥0∞} (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ := by
  let ⟨t, hts, ht, ht0⟩ := exists_measurable_superset_of_null hfg
  have h_ae_not_mem : ∀ᵐ x ∂μ, x ∉ t := by simpa [ae_iff] using ht0
  rw [lintegral, lintegral]
  refine iSup₂_le fun s hsf ↦ le_iSup₂_of_le (s.restrict tᶜ) ?_ ?_
  · intro x
    by_cases hx : x ∈ t
    · rw [SimpleFunc.restrict_apply _ ht.compl,
        Set.indicator_of_notMem (show x ∉ tᶜ by simpa using hx)]
      exact bot_le
    · have hsxg : s x ≤ g x := by
        exact le_trans (hsf x) (by_contra fun hxfg ↦ hx (hts hxfg))
      rw [SimpleFunc.restrict_apply _ ht.compl, indicator_of_mem hx]
      exact hsxg
  · have h_restrict : ∀ᵐ x ∂μ, s x = s.restrict tᶜ x := by
      exact h_ae_not_mem.mono fun x hxt ↦ by
        rw [SimpleFunc.restrict_apply _ ht.compl, indicator_of_mem hxt]
    exact le_of_eq <| SimpleFunc.lintegral_eq_of_measure_preimage
      (SimpleFunc.measure_preimage_singleton_congr_ae (μ := μ) s (s.restrict tᶜ) h_restrict)

theorem lintegral_congr_ae {f g : X → ℝ≥0∞} (hfg : ∀ᵐ x ∂μ, f x = g x) :
    ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ := by
  apply le_antisymm
  · exact lintegral_mono_ae <| hfg.mono fun x hx ↦ hx.le
  · exact lintegral_mono_ae <| hfg.mono fun x hx ↦ hx.ge

end MTI
