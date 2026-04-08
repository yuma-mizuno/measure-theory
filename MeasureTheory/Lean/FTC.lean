import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MeasureTheory.Lean.MathlibAliases

set_option autoImplicit false

namespace MTI

section

open Filter MeasureTheory Topology Asymptotics Metric Set

inductive IsIoc (a : ℝ) (A : ℝ → Set ℝ) : Prop
  | ge : (∀ t, A t = Ioc a t) → IsIoc a A
  | le : (∀ t, A t = Ioc t a) → IsIoc a A

theorem IsIoc.le_or_ge {a : ℝ} {A : ℝ → Set ℝ} (hA : IsIoc a A) :
    (∀ t, A t = Ioc a t) ∨ (∀ t, A t = Ioc t a) := by
  rcases hA with hA | hA <;> simp [hA]

theorem IsIoc.le_top {a : ℝ} {A : ℝ → Set ℝ} (hA : IsIoc a A) (t : ℝ) :
    volume (A t) < ⊤ := by
  rcases hA with hA | hA <;> simp [hA t]

theorem IsIoc.measurable {a : ℝ} {A : ℝ → Set ℝ} (hA : IsIoc a A) (t : ℝ) :
    MeasurableSet (A t) := by
  rcases hA with hA | hA <;> simp [hA t]

theorem IsIoc.integrableOn_const {a : ℝ} (c : ℝ) {A : ℝ → Set ℝ} (hA : IsIoc a A) (t : ℝ) :
    Integrable (fun _ ↦ c) (volume.restrict (A t)) := by
  rcases hA with hA | hA <;> simp [hA t]

theorem Tendsto.hasFiniteIntegralWithin_Icc
    {f : ℝ → ℝ} {a b x c : ℝ} (hf : Tendsto f (𝓝[Icc a b] x) (𝓝 c))
    (hx : x ∈ Icc a b) {A : ℝ → Set ℝ} (hA : IsIoc x A) :
    ∀ᶠ t in 𝓝[Icc a b] x, HasFiniteIntegral f (volume.restrict (A t)) := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ᶠ y in 𝓝[Icc a b] x, |f y| ≤ M :=
    IsBoundedUnder.eventually_le hf.norm.isBoundedUnder_le
  have hM' : ∀ᶠ y in 𝓝 x, y ∈ Icc a b → |f y| ≤ M :=
    (eventually_nhdsWithin_iff.1 hM)
  rcases mem_nhds_iff_exists_Ioo_subset.mp hM' with ⟨u, l, hxIoo, hsub⟩
  rw [eventually_iff_exists_mem]
  refine ⟨Ioo u l ∩ Icc a b, ?_, ?_⟩
  · simpa [inter_comm] using inter_mem_nhdsWithin (Icc a b) (Ioo_mem_nhds hxIoo.1 hxIoo.2)
  intro t ht
  rcases ht with ⟨htIoo, htIcc⟩
  apply HasFiniteIntegral.restrict_of_bounded M (hA.le_top t)
    (ae_restrict_of_forall_mem (hA.measurable t) ?_)
  intro z hz
  have hzIcc : z ∈ Icc a b := by
    rcases hA.le_or_ge with hA' | hA'
    · rw [hA' t] at hz
      exact ⟨le_trans hx.1 hz.1.le, le_trans hz.2 htIcc.2⟩
    · rw [hA' t] at hz
      exact ⟨le_trans htIcc.1 hz.1.le, le_trans hz.2 hx.2⟩
  have hzIoo : z ∈ Ioo u l := by
    rcases hA.le_or_ge with hA' | hA'
    · rw [hA' t] at hz
      exact ⟨lt_trans hxIoo.1 hz.1, lt_of_le_of_lt hz.2 htIoo.2⟩
    · rw [hA' t] at hz
      exact ⟨lt_trans htIoo.1 hz.1, lt_of_le_of_lt hz.2 hxIoo.2⟩
  exact hsub hzIoo hzIcc

theorem Tendsto.integral_sub_linear_isLittleOWithin_Icc {f : ℝ → ℝ} {a b x c : ℝ}
    (hf : Tendsto f (𝓝[Icc a b] x) (𝓝 c)) (hfm : Measurable f) (hx : x ∈ Icc a b)
    (A : ℝ → Set ℝ) (hA : IsIoc x A) :
    (fun t ↦ (∫ y in A t, f y) - volume.real (A t) • c) =o[𝓝[Icc a b] x]
      fun t ↦ volume.real (A t) := by
  rw [isLittleO_iff]
  intro ε ε₀
  have ha : ∀ᶠ t in 𝓝[Icc a b] x, ∀ z ∈ A t, f z ∈ closedBall c ε := by
    have hε : ∀ᶠ y in 𝓝 x, y ∈ Icc a b → f y ∈ closedBall c ε :=
      eventually_nhdsWithin_iff.1 (hf <| closedBall_mem_nhds c ε₀)
    rcases mem_nhds_iff_exists_Ioo_subset.mp hε with ⟨u, l, hxIoo, hsub⟩
    rw [eventually_iff_exists_mem]
    refine ⟨Ioo u l ∩ Icc a b, ?_, ?_⟩
    · simpa [inter_comm] using inter_mem_nhdsWithin (Icc a b) (Ioo_mem_nhds hxIoo.1 hxIoo.2)
    · intro t ht z hz
      rcases ht with ⟨htIoo, htIcc⟩
      have hzIcc : z ∈ Icc a b := by rcases hA.le_or_ge with hA' | hA' <;> grind
      have hzIoo : z ∈ Ioo u l := by rcases hA.le_or_ge with hA' | hA' <;> grind
      exact hsub hzIoo hzIcc
  filter_upwards [hf.hasFiniteIntegralWithin_Icc hx hA, ha] with t ht hεt
  rw [← setIntegral_const]
  rw [← integral_sub ⟨hfm.aestronglyMeasurable, ht⟩ (hA.integrableOn_const c t)]
  simp only [mem_closedBall, dist_eq_norm] at hεt
  simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  apply norm_setIntegral_le_of_norm_le_const (hA.le_top t) hεt

/-- Fundamental theorem of calculus -/
theorem integral_sub_linear_isLittleO_of_tendstoWithin_Icc (f : ℝ → ℝ) {a b x : ℝ}
    (hfm : Measurable f) (hx : x ∈ Icc a b) (hf : ContinuousWithinAt f (Icc a b) x) :
    HasDerivWithinAt (fun t ↦ ∫ y in x..t, f y) (f x) (Icc a b) x := by
  rw [hasDerivWithinAt_iff_isLittleO]
  simp only [intervalIntegral.integral_same, sub_zero, smul_eq_mul]
  have h₁ := Tendsto.integral_sub_linear_isLittleOWithin_Icc hf hfm hx
    (fun t ↦ Ioc x t) (IsIoc.ge fun t ↦ rfl)
  have h₂ := Tendsto.integral_sub_linear_isLittleOWithin_Icc hf hfm hx
    (fun t ↦ Ioc t x) (IsIoc.le fun t ↦ rfl)
  refine ((h₁.trans_le fun t ↦ ?_).sub (h₂.trans_le fun t ↦ ?_)).congr_left fun t ↦ ?_
  · rcases le_total x t with hxt | hxt <;> simp [hxt]
  · rcases le_total x t with hxt | hxt <;> simp [hxt, abs_sub_comm]
  · rcases le_total x t with hxt | htx
    · rw [intervalIntegral.integral_of_le hxt]
      simp [hxt]
    · rw [intervalIntegral.integral_of_ge htx]
      simp only [not_lt, htx, Ioc_eq_empty, Measure.restrict_empty, integral_zero_measure,
        measureReal_empty, smul_eq_mul, zero_mul, sub_self, Real.volume_real_Ioc, sub_nonneg,
        sup_of_le_left, zero_sub, neg_sub]
      ring

theorem hasDerivWithinAt_intervalIntegral_right_of_continuousOn_Icc {f : ℝ → ℝ} {a b x : ℝ}
    (hfm : Measurable f) (hx : x ∈ Icc a b) (hf : ContinuousOn f (Icc a b)) :
    HasDerivWithinAt (fun t ↦ ∫ y in a..t, f y) (f x) (Icc a b) x := by
  have hsplit :
      (fun t ↦ ∫ y in a..t, f y) =ᶠ[𝓝[Icc a b] x]
        fun t ↦ (∫ y in a..x, f y) + ∫ y in x..t, f y := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hf.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1)
      (hf.mono (uIcc_subset_Icc hx ht)).intervalIntegrable]
  exact ((integral_sub_linear_isLittleO_of_tendstoWithin_Icc f hfm hx (hf x hx)).const_add
    (∫ y in a..x, f y)).congr_of_eventuallyEq hsplit (by simp)

theorem integral_eq_sub_of_hasDerivAt_of_le {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfm' : Measurable f') (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) :
    ∫ y in a..b, f' y = f b - f a := by
  let g : ℝ → ℝ := fun t ↦ f t - ∫ y in a..t, f' y
  have hgcont : ContinuousOn g (Icc a b) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt.sub
      (hasDerivWithinAt_intervalIntegral_right_of_continuousOn_Icc hfm' hx hf').continuousWithinAt
  have hgderiv : ∀ x ∈ Ico a b, HasDerivWithinAt g 0 (Ici x) x := by
    intro x hx
    have hfx : HasDerivAt f (f' x) x := hderiv x (Ico_subset_Icc_self hx)
    have hintxIcc :
        HasDerivWithinAt (fun t ↦ ∫ y in a..t, f' y) (f' x) (Icc a b) x :=
      hasDerivWithinAt_intervalIntegral_right_of_continuousOn_Icc hfm' (Ico_subset_Icc_self hx) hf'
    have hintx :
        HasDerivWithinAt (fun t ↦ ∫ y in a..t, f' y) (f' x) (Ici x) x :=
      hintxIcc.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)
    simpa [g, sub_self] using hfx.hasDerivWithinAt.sub hintx
  suffices f b - ∫ (y : ℝ) in a..b, f' y = f a by grind
  simpa only [intervalIntegral.integral_same, sub_zero, g] using
    constant_of_has_deriv_right_zero hgcont hgderiv b ⟨hab, le_rfl⟩

end

end MTI
