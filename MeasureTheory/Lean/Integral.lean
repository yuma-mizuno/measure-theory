import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open MeasureTheory Set Function ENNReal MeasurableSpace Filter

namespace MTI

section

variable {X : Type*}

/-- The positive part of a real-valued function, regarded as an `ℝ≥0∞`-valued function. -/
def posPart (f : X → ℝ) : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (f x)

/-- The negative part of a real-valued function, regarded as an `ℝ≥0∞`-valued function. -/
def negPart (f : X → ℝ) : X → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (-f x)

/-- The sum of the positive and negative parts is the absolute value. -/
theorem posPart_add_negPart_eq_abs {f : X → ℝ} (x : X) :
    posPart f x + negPart f x = ENNReal.ofReal |f x| := by
  by_cases hx : 0 ≤ f x
  · have hneg : -f x ≤ 0 := by linarith
    simp [posPart, negPart, abs_of_nonneg hx, hneg]
  · have hx' : f x ≤ 0 := le_of_not_ge hx
    have hneg : 0 ≤ -f x := by linarith
    simp [posPart, negPart, abs_of_nonpos hx', hx']

theorem posPart_le_abs {f : X → ℝ} (x : X) :
    posPart f x ≤ ENNReal.ofReal |f x| := by
  calc
    posPart f x ≤ posPart f x + negPart f x := by
      exact le_add_of_nonneg_right (by simp)
    _ = ENNReal.ofReal |f x| := posPart_add_negPart_eq_abs (f := f) x

theorem negPart_le_abs {f : X → ℝ} (x : X) :
    negPart f x ≤ ENNReal.ofReal |f x| := by
  calc
    negPart f x ≤ posPart f x + negPart f x := by
      exact le_add_of_nonneg_left (by simp)
    _ = ENNReal.ofReal |f x| := posPart_add_negPart_eq_abs (f := f) x

/-- A real-valued function is the difference of its positive and negative parts. -/
theorem eq_posPart_sub_negPart {f : X → ℝ} (x : X) :
    f x = (posPart f x).toReal - (negPart f x).toReal := by
  by_cases hx : 0 ≤ f x
  · have hneg : -f x ≤ 0 := by linarith
    have hpos : (posPart f x).toReal = f x := by
      simp [posPart, hx]
    have hneg' : (negPart f x).toReal = 0 := by
      change (ENNReal.ofReal (-f x)).toReal = 0
      rw [ENNReal.ofReal_of_nonpos hneg, ENNReal.toReal_zero]
    calc
      f x = f x - 0 := (sub_zero (f x)).symm
      _ = (posPart f x).toReal - 0 := by rw [hpos]
      _ = (posPart f x).toReal - (negPart f x).toReal := by rw [hneg']
  · have hx' : f x ≤ 0 := le_of_not_ge hx
    have hneg : 0 ≤ -f x := by linarith
    calc
      f x = 0 - (-f x) := by ring
      _ = (posPart f x).toReal - (negPart f x).toReal := by
        have hpos : (posPart f x).toReal = 0 := by
          change (ENNReal.ofReal (f x)).toReal = 0
          rw [ENNReal.ofReal_of_nonpos hx', ENNReal.toReal_zero]
        have hneg' : (negPart f x).toReal = -f x := by
          simp [negPart, hneg]
        rw [hpos, hneg']

theorem abs_eq_posPart_add_negPart {f : X → ℝ} (x : X) :
    |f x| = (posPart f x).toReal + (negPart f x).toReal := by
  by_cases hx : 0 ≤ f x
  · have hneg : -f x ≤ 0 := by linarith
    have hpos : (posPart f x).toReal = f x := by
      simp [posPart, hx]
    have hneg' : (negPart f x).toReal = 0 := by
      change (ENNReal.ofReal (-f x)).toReal = 0
      rw [ENNReal.ofReal_of_nonpos hneg, ENNReal.toReal_zero]
    calc
      |f x| = f x := abs_of_nonneg hx
      _ = (posPart f x).toReal + 0 := by rw [hpos]; ring
      _ = (posPart f x).toReal + (negPart f x).toReal := by rw [hneg']
  · have hx' : f x ≤ 0 := le_of_not_ge hx
    have hneg : 0 ≤ -f x := by linarith
    have hpos : (posPart f x).toReal = 0 := by
      change (ENNReal.ofReal (f x)).toReal = 0
      rw [ENNReal.ofReal_of_nonpos hx', ENNReal.toReal_zero]
    have hneg' : (negPart f x).toReal = -f x := by
      simp [negPart, hneg]
    calc
      |f x| = -f x := abs_of_nonpos hx'
      _ = 0 + (negPart f x).toReal := by rw [hneg']; ring
      _ = (posPart f x).toReal + (negPart f x).toReal := by rw [hpos]

theorem negPart_eq_zero_of_nonneg {f : X → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) :
    negPart f = fun _ ↦ 0 := by
  funext x
  have hneg : -f x ≤ 0 := by linarith [hf_nonneg x]
  simp [negPart, hneg]

end

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {Y : Type*} [MeasurableSpace Y]

@[fun_prop, measurability]
theorem measurable_posPart {f : X → ℝ} (hf : Measurable f) : Measurable (posPart f) := by
  simpa [posPart] using hf.ennreal_ofReal

@[fun_prop, measurability]
theorem measurable_negPart {f : X → ℝ} (hf : Measurable f) : Measurable (negPart f) := by
  simpa [negPart] using hf.neg.ennreal_ofReal

/-- A real-valued function has finite integral if the lower integral of its absolute value is
finite. -/
@[fun_prop]
def HasFiniteIntegral (f : X → ℝ) (μ : Measure X) : Prop :=
  ∫⁻ x, ENNReal.ofReal |f x| ∂μ < ∞

section HasFiniteIntegral

theorem hasFiniteIntegral_iff {f : X → ℝ} :
    HasFiniteIntegral f μ ↔ ∫⁻ x, ENNReal.ofReal |f x| ∂μ < ∞ :=
  Iff.rfl

theorem HasFiniteIntegral.ne_top {f : X → ℝ} (hf : HasFiniteIntegral f μ) :
    ∫⁻ x, ENNReal.ofReal |f x| ∂μ ≠ ∞ :=
  ne_of_lt hf

theorem hasFiniteIntegral_of_ne_top {f : X → ℝ}
    (hf : ∫⁻ x, ENNReal.ofReal |f x| ∂μ ≠ ∞) :
    HasFiniteIntegral f μ :=
  lt_of_le_of_ne le_top hf

theorem HasFiniteIntegral.congr_ae {f g : X → ℝ} (hf : HasFiniteIntegral f μ)
    (hfg : f =ᵐ[μ] g) :
    HasFiniteIntegral g μ := by
  refine hasFiniteIntegral_of_ne_top ?_
  have h_abs :
      (fun x ↦ ENNReal.ofReal |g x|) =ᵐ[μ] fun x ↦ ENNReal.ofReal |f x| :=
    hfg.symm.mono fun x hx ↦ by simp [hx]
  rw [lintegral_congr_ae h_abs]
  exact hf.ne_top

theorem HasFiniteIntegral.comp_measurable {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    {f : Z → X} {g : X → ℝ} (hg : HasFiniteIntegral g (Measure.map f ν))
    (hg_meas : Measurable g) (hf : Measurable f) :
    HasFiniteIntegral (g ∘ f) ν := by
  refine hasFiniteIntegral_of_ne_top ?_
  have h_abs_meas : Measurable fun x ↦ ENNReal.ofReal |g x| := by
    simpa using (continuous_abs.measurable.comp hg_meas).ennreal_ofReal
  have h_map :
      ∫⁻ x, ENNReal.ofReal |(g ∘ f) x| ∂ν =
        ∫⁻ y, ENNReal.ofReal |g y| ∂(Measure.map f ν) := by
    simpa [Function.comp] using (lintegral_map h_abs_meas hf).symm
  rw [h_map]
  exact hg.ne_top

theorem HasFiniteIntegral.abs {f : X → ℝ} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun x ↦ |f x|) μ := by
  refine hasFiniteIntegral_of_ne_top ?_
  simpa using hf.ne_top

theorem HasFiniteIntegral.abs_add_abs_ne_top {f g : X → ℝ}
    (hf : HasFiniteIntegral f μ) (hg : HasFiniteIntegral g μ)
    (hf_meas : Measurable f) (hg_meas : Measurable g) :
    ∫⁻ x, ENNReal.ofReal (|f x| + |g x|) ∂μ ≠ ∞ := by
  have h_abs_meas : Measurable fun x ↦ |f x| := continuous_abs.measurable.comp hf_meas
  have h_absg_meas : Measurable fun x ↦ |g x| := continuous_abs.measurable.comp hg_meas
  calc
    ∫⁻ x, ENNReal.ofReal (|f x| + |g x|) ∂μ
        = ∫⁻ x, ENNReal.ofReal |f x| + ENNReal.ofReal |g x| ∂μ := by
      refine lintegral_congr fun x ↦ ?_
      rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ = (∫⁻ x, ENNReal.ofReal |f x| ∂μ) + ∫⁻ x, ENNReal.ofReal |g x| ∂μ := by
      rw [lintegral_add_left (by simpa using h_abs_meas.ennreal_ofReal)]
    _ ≠ ∞ := add_ne_top.mpr ⟨hf.ne_top, hg.ne_top⟩

theorem HasFiniteIntegral.add {f g : X → ℝ}
    (hf : HasFiniteIntegral f μ) (hg : HasFiniteIntegral g μ)
    (hf_meas : Measurable f) (_hg_meas : Measurable g) :
    HasFiniteIntegral (fun x ↦ f x + g x) μ := by
  refine hasFiniteIntegral_of_ne_top ?_
  refine ne_top_of_le_ne_top (hf.abs_add_abs_ne_top hg hf_meas _hg_meas) ?_
  refine lintegral_mono fun x ↦ ?_
  exact ENNReal.ofReal_le_ofReal <| by
    have hsum_nonneg : 0 ≤ |f x| + |g x| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa [abs_of_nonneg hsum_nonneg] using
      abs_add_le (f x) (g x)

theorem HasFiniteIntegral.sub {f g : X → ℝ}
    (hf : HasFiniteIntegral f μ) (hg : HasFiniteIntegral g μ)
    (hf_meas : Measurable f) (_hg_meas : Measurable g) :
    HasFiniteIntegral (fun x ↦ f x - g x) μ := by
  refine hasFiniteIntegral_of_ne_top ?_
  refine ne_top_of_le_ne_top (hf.abs_add_abs_ne_top hg hf_meas _hg_meas) ?_
  refine lintegral_mono fun x ↦ ?_
  exact ENNReal.ofReal_le_ofReal <| by
    have hsum_nonneg : 0 ≤ |f x| + |g x| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa [sub_eq_add_neg, abs_neg, abs_of_nonneg hsum_nonneg] using
      abs_add_le (f x) (-g x)

theorem HasFiniteIntegral.max {f g : X → ℝ}
    (hf : HasFiniteIntegral f μ) (hg : HasFiniteIntegral g μ)
    (hf_meas : Measurable f) (_hg_meas : Measurable g) :
    HasFiniteIntegral (fun x ↦ max (f x) (g x)) μ := by
  refine hasFiniteIntegral_of_ne_top ?_
  refine ne_top_of_le_ne_top (hf.abs_add_abs_ne_top hg hf_meas _hg_meas) ?_
  refine lintegral_mono fun x ↦ ?_
  exact ENNReal.ofReal_le_ofReal <| by
    have hsum_nonneg : 0 ≤ |f x| + |g x| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hmax : |Max.max (f x) (g x)| ≤ |f x| + |g x| := by
      by_cases h : f x ≤ g x
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (abs_nonneg (f x))
      · rw [max_eq_left (lt_of_not_ge h).le]
        exact le_add_of_nonneg_right (abs_nonneg (g x))
    simpa [abs_of_nonneg hsum_nonneg] using hmax

theorem hasFiniteIntegral_of_nonneg {f : X → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_fin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞) :
    HasFiniteIntegral f μ := by
  refine hasFiniteIntegral_of_ne_top ?_
  have habs : (fun x ↦ ENNReal.ofReal |f x|) = fun x ↦ ENNReal.ofReal (f x) := by
    funext x
    simp [abs_of_nonneg (hf_nonneg x)]
  rw [habs]
  exact hf_fin

theorem HasFiniteIntegral.lintegral_ne_top_of_nonneg {f : X → ℝ} (hf : HasFiniteIntegral f μ)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ := by
  have habs : (fun x ↦ ENNReal.ofReal |f x|) = fun x ↦ ENNReal.ofReal (f x) := by
    funext x
    simp [abs_of_nonneg (hf_nonneg x)]
  simpa [habs] using hf.ne_top

theorem HasFiniteIntegral.pos_ne_top {f : X → ℝ} (hf : HasFiniteIntegral f μ) :
    ∫⁻ x, posPart f x ∂μ ≠ ∞ := by
  refine ne_top_of_le_ne_top hf.ne_top ?_
  exact lintegral_mono fun x ↦ posPart_le_abs (f := f) x

theorem HasFiniteIntegral.neg_ne_top {f : X → ℝ} (hf : HasFiniteIntegral f μ) :
    ∫⁻ x, negPart f x ∂μ ≠ ∞ := by
  refine ne_top_of_le_ne_top hf.ne_top ?_
  exact lintegral_mono fun x ↦ negPart_le_abs (f := f) x

end HasFiniteIntegral

section Lintegral

theorem lintegral_posPart_sub_eq_lintegral_max_sub_lintegral {f g : X → ℝ}
    (hg : HasFiniteIntegral g μ) (hg_meas : Measurable g) (hg_nonneg : ∀ x, 0 ≤ g x) :
    ∫⁻ x, posPart (fun x ↦ f x - g x) x ∂μ
      = (∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ) -
          ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  calc
    ∫⁻ x, posPart (fun x ↦ f x - g x) x ∂μ
        = ∫⁻ x, ENNReal.ofReal (f x) - ENNReal.ofReal (g x) ∂μ := by
      refine lintegral_congr fun x ↦ ?_
      simp [posPart, ENNReal.ofReal_sub, hg_nonneg x]
    _ = ∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x))
          - ENNReal.ofReal (g x) ∂μ := by
      refine lintegral_congr fun x ↦ ?_
      by_cases h : ENNReal.ofReal (f x) ≤ ENNReal.ofReal (g x)
      · rw [tsub_eq_zero_of_le h, max_eq_right h, tsub_eq_zero_of_le le_rfl]
      · rw [max_eq_left (lt_of_not_ge h).le]
    _ = (∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ) -
          ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
      exact lintegral_sub
        (by simpa using hg_meas.ennreal_ofReal)
        (hg.lintegral_ne_top_of_nonneg hg_nonneg)
        (ae_of_all _ fun x ↦ le_max_right _ _)

theorem lintegral_negPart_sub_eq_lintegral_max_sub_lintegral {f g : X → ℝ}
    (hf : HasFiniteIntegral f μ) (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x) :
    ∫⁻ x, negPart (fun x ↦ f x - g x) x ∂μ
      = (∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ) -
          ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  calc
    ∫⁻ x, negPart (fun x ↦ f x - g x) x ∂μ
        = ∫⁻ x, ENNReal.ofReal (g x) - ENNReal.ofReal (f x) ∂μ := by
      refine lintegral_congr fun x ↦ ?_
      have hx : -(f x - g x) = g x - f x := by ring
      simp [negPart, hx, ENNReal.ofReal_sub, hf_nonneg x]
    _ = ∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x))
          - ENNReal.ofReal (f x) ∂μ := by
      refine lintegral_congr fun x ↦ ?_
      by_cases h : ENNReal.ofReal (g x) ≤ ENNReal.ofReal (f x)
      · rw [tsub_eq_zero_of_le h, max_eq_left h, tsub_eq_zero_of_le le_rfl]
      · rw [max_eq_right (lt_of_not_ge h).le]
    _ = (∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ) -
          ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
      exact lintegral_sub
        (by simpa using hf_meas.ennreal_ofReal)
        (hf.lintegral_ne_top_of_nonneg hf_nonneg)
        (ae_of_all _ fun x ↦ le_max_left _ _)

theorem toReal_lintegral_max_sub_lintegral_right_of_nonneg {f g : X → ℝ}
    (hf : HasFiniteIntegral f μ) (hg : HasFiniteIntegral g μ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x) :
    ((∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ) -
        ∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal
      = (∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ).toReal
          - (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal := by
  rw [ENNReal.toReal_sub_of_le
      (lintegral_mono fun _ ↦ le_max_right _ _)]
  simpa [ENNReal.ofReal_max] using
    (hf.max hg hf_meas hg_meas).lintegral_ne_top_of_nonneg fun x ↦ by
      by_cases h : f x ≤ g x
      · rw [max_eq_right h]
        exact hg_nonneg x
      · rw [max_eq_left (lt_of_not_ge h).le]
        exact hf_nonneg x

theorem toReal_lintegral_max_sub_lintegral_left_of_nonneg {f g : X → ℝ}
    (hf : HasFiniteIntegral f μ) (hg : HasFiniteIntegral g μ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x) :
    ((∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ) -
        ∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal
      = (∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ).toReal
          - (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
  rw [ENNReal.toReal_sub_of_le
      (lintegral_mono fun _ ↦ le_max_left _ _)]
  simpa [ENNReal.ofReal_max] using
    (hf.max hg hf_meas hg_meas).lintegral_ne_top_of_nonneg fun x ↦ by
      by_cases h : f x ≤ g x
      · rw [max_eq_right h]
        exact hg_nonneg x
      · rw [max_eq_left (lt_of_not_ge h).le]
        exact hf_nonneg x

end Lintegral

/-- A real-valued function is integrable if it is measurable and has finite integral. -/
structure Integrable (f : X → ℝ) (μ : Measure X) : Prop where
  measurable : Measurable f
  hasFiniteIntegral : HasFiniteIntegral f μ

section Integrable

theorem Integrable.abs_ne_top {f : X → ℝ} (hf : Integrable f μ) :
    ∫⁻ x, ENNReal.ofReal |f x| ∂μ ≠ ∞ :=
  hf.hasFiniteIntegral.ne_top

theorem Integrable.abs {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun x ↦ |f x|) μ :=
  ⟨continuous_abs.measurable.comp hf.measurable, hf.hasFiniteIntegral.abs⟩

theorem Integrable.comp_measurable {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    {f : Z → X} {g : X → ℝ} (hg : Integrable g (Measure.map f ν)) (hf : Measurable f) :
    Integrable (g ∘ f) ν := by
  exact ⟨hg.measurable.comp hf, hg.hasFiniteIntegral.comp_measurable hg.measurable hf⟩

theorem integrable_of_ae_eq {f g : X → ℝ} (hf_meas : Measurable f) (hg : Integrable g μ)
    (hfg : f =ᵐ[μ] g) :
    Integrable f μ := by
  exact ⟨hf_meas, hg.hasFiniteIntegral.congr_ae hfg.symm⟩

theorem integrable_of_nonneg {f : X → ℝ} (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_fin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞) :
    Integrable f μ := by
  exact ⟨hf_meas, hasFiniteIntegral_of_nonneg hf_nonneg hf_fin⟩

theorem Integrable.sub {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x ↦ f x - g x) μ := by
  exact ⟨hf.measurable.sub hg.measurable,
    hf.hasFiniteIntegral.sub hg.hasFiniteIntegral hf.measurable hg.measurable⟩

theorem Integrable.add {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x ↦ f x + g x) μ := by
  exact ⟨hf.measurable.add hg.measurable,
    hf.hasFiniteIntegral.add hg.hasFiniteIntegral hf.measurable hg.measurable⟩

theorem Integrable.neg {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun x ↦ -f x) μ := by
  refine ⟨hf.measurable.neg, ?_⟩
  refine hasFiniteIntegral_of_ne_top ?_
  simpa [abs_neg] using hf.abs_ne_top

theorem Integrable.const_mul {f : X → ℝ} (hf : Integrable f μ) (c : ℝ) :
    Integrable (fun x ↦ c * f x) μ := by
  refine ⟨hf.measurable.const_mul c, ?_⟩
  refine hasFiniteIntegral_of_ne_top ?_
  have h_abs_meas : Measurable fun x ↦ ENNReal.ofReal |f x| := by
    simpa using (continuous_abs.measurable.comp hf.measurable).ennreal_ofReal
  calc
    ∫⁻ x, ENNReal.ofReal |c * f x| ∂μ
        = ∫⁻ x, ENNReal.ofReal |c| * ENNReal.ofReal |f x| ∂μ := by
      refine lintegral_congr fun x ↦ ?_
      rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
    _ = ENNReal.ofReal |c| * ∫⁻ x, ENNReal.ofReal |f x| ∂μ := by
      rw [lintegral_const_mul _ h_abs_meas]
    _ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.abs_ne_top

theorem Integrable.lintegral_ne_top_of_nonneg {f : X → ℝ} (hf : Integrable f μ)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞ :=
  hf.hasFiniteIntegral.lintegral_ne_top_of_nonneg hf_nonneg

theorem Integrable.max_hasFiniteIntegral {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    HasFiniteIntegral (fun x ↦ max (f x) (g x)) μ :=
  hf.hasFiniteIntegral.max hg.hasFiniteIntegral hf.measurable hg.measurable

theorem Integrable.posPart_ne_top {f : X → ℝ} (hf : Integrable f μ) :
    ∫⁻ x, posPart f x ∂μ ≠ ∞ :=
  hf.hasFiniteIntegral.pos_ne_top

theorem Integrable.negPart_ne_top {f : X → ℝ} (hf : Integrable f μ) :
    ∫⁻ x, negPart f x ∂μ ≠ ∞ :=
  hf.hasFiniteIntegral.neg_ne_top

theorem Integrable.posPart_toReal {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun x ↦ (posPart f x).toReal) μ :=
  integrable_of_nonneg
    (by simpa using (measurable_posPart hf.measurable).ennreal_toReal)
    (fun _ ↦ by simp)
    (by simpa [posPart] using hf.posPart_ne_top)

theorem Integrable.negPart_toReal {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun x ↦ (negPart f x).toReal) μ :=
  integrable_of_nonneg
    (by simpa using (measurable_negPart hf.measurable).ennreal_toReal)
    (fun _ ↦ by simp)
    (by simpa [negPart] using hf.negPart_ne_top)

theorem integrable_zero : Integrable (fun _ : X ↦ (0 : ℝ)) μ :=
  integrable_of_nonneg measurable_const (fun _ ↦ le_rfl) (by simp)

end Integrable

/-- `f` admits an integrable representative in its almost-everywhere class. -/
def HasIntegrableRep (f : X → ℝ) (μ : Measure X) : Prop :=
  ∃ g, Integrable g μ ∧ f =ᵐ[μ] g

noncomputable def integrableRep {f : X → ℝ} {μ : Measure X} (h : HasIntegrableRep f μ) : X → ℝ :=
  Classical.choose h

theorem integrableRep_integrable {f : X → ℝ} {μ : Measure X} (h : HasIntegrableRep f μ) :
    Integrable (integrableRep h) μ :=
  (Classical.choose_spec h).1

theorem ae_eq_integrableRep {f : X → ℝ} {μ : Measure X} (h : HasIntegrableRep f μ) :
    f =ᵐ[μ] integrableRep h :=
  (Classical.choose_spec h).2

theorem hasIntegrableRep_iff_integrable {f : X → ℝ} (hf_meas : Measurable f) :
    HasIntegrableRep f μ ↔ Integrable f μ := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    exact integrable_of_ae_eq hf_meas hg hfg
  · intro hf
    exact ⟨f, hf, Filter.EventuallyEq.rfl⟩

theorem hasIntegrableRep_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[μ] g) :
    HasIntegrableRep f μ ↔ HasIntegrableRep g μ := by
  constructor
  · rintro ⟨u, hu, hfu⟩
    exact ⟨u, hu, hfg.symm.trans hfu⟩
  · rintro ⟨u, hu, hgu⟩
    exact ⟨u, hu, hfg.trans hgu⟩

open Classical in
/-- The Lebesgue integral of a real-valued function, defined using any integrable representative
in its almost-everywhere class, and `0` if no such representative exists. -/
def integral (μ : Measure X) (f : X → ℝ) : ℝ :=
  if h : HasIntegrableRep f μ then
    (∫⁻ x, posPart (integrableRep h) x ∂μ).toReal -
      (∫⁻ x, negPart (integrableRep h) x ∂μ).toReal
  else
    0

notation3 (priority := high) "∫ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => integral μ r

theorem integral_eq_lintegral_posPart_sub_lintegral_negPart_of_ae_eq {f g : X → ℝ}
    (hg : Integrable g μ) (hfg : f =ᵐ[μ] g) :
    ∫ x, f x ∂μ = (∫⁻ x, posPart g x ∂μ).toReal - (∫⁻ x, negPart g x ∂μ).toReal := by
  let h : HasIntegrableRep f μ := ⟨g, hg, hfg⟩
  rw [integral, dif_pos h]
  have hrep : integrableRep h =ᵐ[μ] g := (ae_eq_integrableRep h).symm.trans hfg
  congr 1
  · simpa [integrableRep] using congrArg ENNReal.toReal <| lintegral_congr_ae <|
      hrep.mono fun x hx ↦ by
        simpa [posPart] using congrArg ENNReal.ofReal hx
  · simpa [integrableRep] using congrArg ENNReal.toReal <| lintegral_congr_ae <|
      hrep.mono fun x hx ↦ by
        simpa [negPart] using congrArg (fun t : ℝ => ENNReal.ofReal (-t)) hx

theorem integral_eq_lintegral_posPart_sub_lintegral_negPart {f : X → ℝ} (hf : Integrable f μ) :
    ∫ x, f x ∂μ = (∫⁻ x, posPart f x ∂μ).toReal - (∫⁻ x, negPart f x ∂μ).toReal :=
  integral_eq_lintegral_posPart_sub_lintegral_negPart_of_ae_eq hf Filter.EventuallyEq.rfl

theorem integral_congr_ae {f g : X → ℝ} (hfg : f =ᵐ[μ] g) :
    ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  by_cases h : HasIntegrableRep f μ
  · rcases h with ⟨u, hu, hfu⟩
    rw [integral_eq_lintegral_posPart_sub_lintegral_negPart_of_ae_eq hu hfu,
      integral_eq_lintegral_posPart_sub_lintegral_negPart_of_ae_eq hu (hfg.symm.trans hfu)]
  · have h' : ¬ HasIntegrableRep g μ := by
      intro hg
      exact h ((hasIntegrableRep_congr_ae hfg).2 hg)
    rw [integral, dif_neg h, integral, dif_neg h']

theorem integral_eq_zero_of_not_integrable {f : X → ℝ} (hf_meas : Measurable f)
    (hf_not : ¬ Integrable f μ) :
    ∫ x, f x ∂μ = 0 := by
  rw [integral, dif_neg]
  intro h
  exact hf_not ((hasIntegrableRep_iff_integrable hf_meas).mp h)

theorem integrable_map_iff {f : Y → ℝ} {g : X → Y} (hf : Measurable f) (hg : Measurable g) :
    Integrable f (Measure.map g μ) ↔ Integrable (fun x ↦ f (g x)) μ := by
  constructor
  · intro hf_int
    exact hf_int.comp_measurable hg
  · intro hcomp
    refine ⟨hf, ?_⟩
    have h_abs_meas : Measurable fun y ↦ ENNReal.ofReal |f y| := by
      simpa using (continuous_abs.measurable.comp hf).ennreal_ofReal
    refine hasFiniteIntegral_of_ne_top ?_
    rw [lintegral_map h_abs_meas hg]
    exact hcomp.abs_ne_top

theorem integral_map {f : Y → ℝ} {g : X → Y} (hf : Measurable f) (hg : Measurable g) :
    ∫ y, f y ∂(Measure.map g μ) = ∫ x, f (g x) ∂μ := by
  by_cases hf_int : Integrable f (Measure.map g μ)
  · have hcomp_int : Integrable (fun x ↦ f (g x)) μ := (integrable_map_iff hf hg).mp hf_int
    rw [integral_eq_lintegral_posPart_sub_lintegral_negPart hf_int,
      integral_eq_lintegral_posPart_sub_lintegral_negPart hcomp_int]
    congr 1
    · apply congrArg ENNReal.toReal
      calc
        ∫⁻ y, posPart f y ∂(Measure.map g μ) = ∫⁻ x, posPart f (g x) ∂μ := by
            exact lintegral_map (measurable_posPart hf) hg
        _ = ∫⁻ x, posPart (fun x ↦ f (g x)) x ∂μ := by
            refine lintegral_congr fun x ↦ ?_
            simp [posPart]
    · apply congrArg ENNReal.toReal
      calc
        ∫⁻ y, negPart f y ∂(Measure.map g μ) = ∫⁻ x, negPart f (g x) ∂μ := by
            exact lintegral_map (measurable_negPart hf) hg
        _ = ∫⁻ x, negPart (fun x ↦ f (g x)) x ∂μ := by
            refine lintegral_congr fun x ↦ ?_
            simp [negPart]
  · have hcomp_not : ¬ Integrable (fun x ↦ f (g x)) μ := by
      intro hcomp_int
      exact hf_int ((integrable_map_iff hf hg).mpr hcomp_int)
    rw [integral_eq_zero_of_not_integrable hf hf_int]
    symm
    simpa [Function.comp] using
      (integral_eq_zero_of_not_integrable (μ := μ) (f := f ∘ g) (hf.comp hg) hcomp_not)

theorem integral_eq_lintegral_of_nonneg {f : X → ℝ} (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    ∫ x, f x ∂μ = (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
  by_cases hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∞
  · have hf_not : ¬ Integrable f μ := by
      intro hf_int
      exact (hf_int.lintegral_ne_top_of_nonneg hf_nonneg) hfin
    rw [integral_eq_zero_of_not_integrable hf_meas hf_not, hfin, ENNReal.toReal_top]
  · have hf_int : Integrable f μ := integrable_of_nonneg hf_meas hf_nonneg hfin
    rw [integral_eq_lintegral_posPart_sub_lintegral_negPart hf_int]
    simp [posPart, negPart_eq_zero_of_nonneg hf_nonneg]

theorem integral_nonneg {f : X → ℝ} (hf : Integrable f μ) (hf_nonneg : ∀ x, 0 ≤ f x) :
    0 ≤ ∫ x, f x ∂μ := by
  rw [integral_eq_lintegral_of_nonneg hf.measurable hf_nonneg]
  exact ENNReal.toReal_nonneg

theorem integral_add_eq_integral_add_of_nonneg
    {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x) :
    ∫ x, (f x + g x) ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := by
  calc
    ∫ x, (f x + g x) ∂μ
        = (∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ).toReal := by
      rw [integral_eq_lintegral_of_nonneg (hf.measurable.add hg.measurable)
        (fun x ↦ add_nonneg (hf_nonneg x) (hg_nonneg x))]
    _ = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ) + ∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal := by
      apply congrArg ENNReal.toReal
      calc
        ∫⁻ x, ENNReal.ofReal (f x + g x) ∂μ
            = ∫⁻ x, ENNReal.ofReal (f x) + ENNReal.ofReal (g x) ∂μ := by
          refine lintegral_congr fun x ↦ ?_
          rw [ENNReal.ofReal_add (hf_nonneg x) (hg_nonneg x)]
        _ = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) + ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
          rw [lintegral_add_left (by simpa using hf.measurable.ennreal_ofReal)]
    _ = (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal + (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal := by
      rw [ENNReal.toReal_add
        (hf.lintegral_ne_top_of_nonneg hf_nonneg)
        (hg.lintegral_ne_top_of_nonneg hg_nonneg)]
    _ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := by
      rw [integral_eq_lintegral_of_nonneg hf.measurable hf_nonneg,
        integral_eq_lintegral_of_nonneg hg.measurable hg_nonneg]

theorem integral_sub_eq_integral_sub_of_nonneg
    {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x) :
    ∫ x, (f x - g x) ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ := by
  calc
    ∫ x, (f x - g x) ∂μ
        = (∫⁻ x, posPart (fun x ↦ f x - g x) x ∂μ).toReal
            - (∫⁻ x, negPart (fun x ↦ f x - g x) x ∂μ).toReal := by
      rw [integral_eq_lintegral_posPart_sub_lintegral_negPart (hf.sub hg)]
    _ = ((∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ) -
            ∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal
          - (∫⁻ x, negPart (fun x ↦ f x - g x) x ∂μ).toReal := by
      rw [congrArg ENNReal.toReal <|
        lintegral_posPart_sub_eq_lintegral_max_sub_lintegral
          hg.hasFiniteIntegral hg.measurable hg_nonneg]
    _ = ((∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ) -
            ∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal
          - ((∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ) -
              ∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
      rw [congrArg ENNReal.toReal <|
        lintegral_negPart_sub_eq_lintegral_max_sub_lintegral
          hf.hasFiniteIntegral hf.measurable hf_nonneg]
    _ = ((∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ).toReal
          - (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal)
        - ((∫⁻ x, max (ENNReal.ofReal (f x)) (ENNReal.ofReal (g x)) ∂μ).toReal
            - (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal) := by
      rw [toReal_lintegral_max_sub_lintegral_right_of_nonneg
          hf.hasFiniteIntegral hg.hasFiniteIntegral hf.measurable hg.measurable hf_nonneg hg_nonneg,
        toReal_lintegral_max_sub_lintegral_left_of_nonneg
          hf.hasFiniteIntegral hg.hasFiniteIntegral hf.measurable hg.measurable hf_nonneg hg_nonneg]
    _ = (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal - (∫⁻ x, ENNReal.ofReal (g x) ∂μ).toReal := by
      ring
    _ = ∫ x, f x ∂μ - ∫ x, g x ∂μ := by
      rw [integral_eq_lintegral_of_nonneg hf.measurable hf_nonneg,
        integral_eq_lintegral_of_nonneg hg.measurable hg_nonneg]

/-- The integral of an integrable function is the difference of the integrals of its positive and
negative parts. -/
theorem integral_eq_integral_posPart_sub_integral_negPart {f : X → ℝ} (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ x, (posPart f x).toReal ∂μ - ∫ x, (negPart f x).toReal ∂μ := by
  calc
    ∫ x, f x ∂μ = ∫ x, ((posPart f x).toReal - (negPart f x).toReal) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ eq_posPart_sub_negPart (f := f) x
    _ = ∫ x, (posPart f x).toReal ∂μ - ∫ x, (negPart f x).toReal ∂μ := by
      exact integral_sub_eq_integral_sub_of_nonneg
        hf.posPart_toReal hf.negPart_toReal
        (fun _ ↦ by simp) (fun _ ↦ by simp)

theorem integral_sub_eq_integral_sub {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x - g x) ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ := by
  have hf_pos : Integrable (fun x ↦ (posPart f x).toReal) μ := hf.posPart_toReal
  have hf_neg : Integrable (fun x ↦ (negPart f x).toReal) μ := hf.negPart_toReal
  have hg_pos : Integrable (fun x ↦ (posPart g x).toReal) μ := hg.posPart_toReal
  have hg_neg : Integrable (fun x ↦ (negPart g x).toReal) μ := hg.negPart_toReal
  calc
    ∫ x, (f x - g x) ∂μ
      = ∫ x, ((posPart f x).toReal + (negPart g x).toReal
          - ((negPart f x).toReal + (posPart g x).toReal)) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            change f x - g x =
              (posPart f x).toReal + (negPart g x).toReal
                - ((negPart f x).toReal + (posPart g x).toReal)
            rw [eq_posPart_sub_negPart (f := f) x, eq_posPart_sub_negPart (f := g) x]
            ring
    _ = ∫ x, ((posPart f x).toReal + (negPart g x).toReal) ∂μ
        - ∫ x, ((negPart f x).toReal + (posPart g x).toReal) ∂μ := by
          exact integral_sub_eq_integral_sub_of_nonneg
            (hf_pos.add hg_neg) (hf_neg.add hg_pos)
            (fun x ↦ add_nonneg (by simp) (by simp))
            (fun x ↦ add_nonneg (by simp) (by simp))
    _ = (∫ x, (posPart f x).toReal ∂μ + ∫ x, (negPart g x).toReal ∂μ)
        - (∫ x, (negPart f x).toReal ∂μ + ∫ x, (posPart g x).toReal ∂μ) := by
          rw [integral_add_eq_integral_add_of_nonneg hf_pos hg_neg
              (fun _ ↦ by simp) (fun _ ↦ by simp),
            integral_add_eq_integral_add_of_nonneg hf_neg hg_pos
              (fun _ ↦ by simp) (fun _ ↦ by simp)]
    _ = ∫ x, f x ∂μ - ∫ x, g x ∂μ := by
          rw [integral_eq_integral_posPart_sub_integral_negPart hf,
            integral_eq_integral_posPart_sub_integral_negPart hg]
          ring

theorem integral_zero : ∫ _x, (0 : ℝ) ∂μ = 0 := by
  simpa [lintegral_zero] using
    (integral_eq_lintegral_of_nonneg (μ := μ) (f := fun _ : X ↦ (0 : ℝ))
      measurable_const (fun _ ↦ le_rfl))

theorem integral_neg {f : X → ℝ} (hf : Integrable f μ) :
    ∫ x, -f x ∂μ = -∫ x, f x ∂μ := by
  calc
    ∫ x, -f x ∂μ = ∫ x, ((0 : ℝ) - f x) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by simp
    _ = ∫ x, (0 : ℝ) ∂μ - ∫ x, f x ∂μ := by
      exact integral_sub_eq_integral_sub integrable_zero hf
    _ = -∫ x, f x ∂μ := by
      rw [integral_zero, zero_sub]

theorem integral_add_eq_integral_add {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x + g x) ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := by
  calc
    ∫ x, (f x + g x) ∂μ = ∫ x, (f x - (-g x)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring
    _ = ∫ x, f x ∂μ - ∫ x, -g x ∂μ := by
      exact integral_sub_eq_integral_sub hf hg.neg
    _ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := by
      rw [integral_neg hg]
      ring

theorem integral_const_mul_eq_const_mul_integral_of_nonneg {f : X → ℝ}
    (hf : Integrable f μ) (hf_nonneg : ∀ x, 0 ≤ f x) {c : ℝ} (hc : 0 ≤ c) :
    ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ := by
  calc
    ∫ x, c * f x ∂μ = (∫⁻ x, ENNReal.ofReal (c * f x) ∂μ).toReal := by
      rw [integral_eq_lintegral_of_nonneg (hf.measurable.const_mul c)
        (fun x ↦ mul_nonneg hc (hf_nonneg x))]
    _ = (ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
      apply congrArg ENNReal.toReal
      calc
        ∫⁻ x, ENNReal.ofReal (c * f x) ∂μ
            = ∫⁻ x, ENNReal.ofReal c * ENNReal.ofReal (f x) ∂μ := by
          refine lintegral_congr fun x ↦ ?_
          rw [ENNReal.ofReal_mul hc]
        _ = ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
          rw [lintegral_const_mul _ (by simpa using hf.measurable.ennreal_ofReal)]
    _ = c * (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
    _ = c * ∫ x, f x ∂μ := by
      rw [integral_eq_lintegral_of_nonneg hf.measurable hf_nonneg]

theorem integral_const_mul_of_nonneg {f : X → ℝ} (hf : Integrable f μ) {c : ℝ} (hc : 0 ≤ c) :
    ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ := by
  calc
    ∫ x, c * f x ∂μ
        = ∫ x, (c * (posPart f x).toReal - c * (negPart f x).toReal) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change c * f x = c * (posPart f x).toReal - c * (negPart f x).toReal
        rw [eq_posPart_sub_negPart (f := f) x]
        ring
    _ = ∫ x, c * (posPart f x).toReal ∂μ - ∫ x, c * (negPart f x).toReal ∂μ := by
      exact integral_sub_eq_integral_sub_of_nonneg
        (hf.posPart_toReal.const_mul c) (hf.negPart_toReal.const_mul c)
        (fun x ↦ mul_nonneg hc (by simp))
        (fun x ↦ mul_nonneg hc (by simp))
    _ = c * ∫ x, (posPart f x).toReal ∂μ - c * ∫ x, (negPart f x).toReal ∂μ := by
      rw [integral_const_mul_eq_const_mul_integral_of_nonneg hf.posPart_toReal (fun _ ↦ by simp) hc,
        integral_const_mul_eq_const_mul_integral_of_nonneg hf.negPart_toReal (fun _ ↦ by simp) hc]
    _ = c * ∫ x, f x ∂μ := by
      rw [integral_eq_integral_posPart_sub_integral_negPart hf]
      ring

theorem integral_const_mul (c : ℝ) {f : X → ℝ} (hf : Integrable f μ) :
    ∫ x, c * f x ∂μ = c * ∫ x, f x ∂μ := by
  by_cases hc : 0 ≤ c
  · exact integral_const_mul_of_nonneg hf hc
  · have hc' : 0 ≤ -c := by linarith
    calc
      ∫ x, c * f x ∂μ = ∫ x, -((-c) * f x) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by ring
      _ = -∫ x, (-c) * f x ∂μ := by
        exact integral_neg (hf.const_mul (-c))
      _ = -((-c) * ∫ x, f x ∂μ) := by
        rw [integral_const_mul_of_nonneg hf hc']
      _ = c * ∫ x, f x ∂μ := by
        ring

theorem abs_integral_le_integral_abs {f : X → ℝ} (hf : Integrable f μ) :
    |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
  calc
    |∫ x, f x ∂μ|
        = |∫ x, (posPart f x).toReal ∂μ - ∫ x, (negPart f x).toReal ∂μ| := by
      rw [integral_eq_integral_posPart_sub_integral_negPart hf]
    _ ≤ ∫ x, (posPart f x).toReal ∂μ + ∫ x, (negPart f x).toReal ∂μ := by
      refine abs_le.mpr ?_
      constructor <;> linarith
        [integral_nonneg hf.posPart_toReal (fun _ ↦ by simp),
          integral_nonneg hf.negPart_toReal (fun _ ↦ by simp)]
    _ = ∫ x, |f x| ∂μ := by
      symm
      calc
        ∫ x, |f x| ∂μ = ∫ x, (posPart f x).toReal + (negPart f x).toReal ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ abs_eq_posPart_add_negPart (f := f) x
        _ = ∫ x, (posPart f x).toReal ∂μ + ∫ x, (negPart f x).toReal ∂μ := by
          exact integral_add_eq_integral_add hf.posPart_toReal hf.negPart_toReal

/-- Dominated convergence theorem for real-valued measurable functions. -/
theorem tendsto_integral_of_dominated_convergence
    {F : ℕ → X → ℝ} {f bound : X → ℝ}
    (hF_meas : ∀ n, Measurable (F n)) (h_bound_int : Integrable bound μ)
    (h_bound : ∀ n x, |F n x| ≤ bound x)
    (h_lim : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (nhds (∫ x, f x ∂μ)) := by
  have h_bound_nonneg : ∀ x, 0 ≤ bound x := by
    intro x
    exact le_trans (abs_nonneg (F 0 x)) (h_bound 0 x)
  have hf_meas : Measurable f := by
    exact measurable_of_tendsto_metrizable hF_meas (tendsto_pi_nhds.2 h_lim)
  have h_abs_f_le : ∀ x, |f x| ≤ bound x := by
    intro x
    have h_closed : IsClosed (Set.Icc (-bound x) (bound x)) := isClosed_Icc
    have h_mem :
        ∀ᶠ n in atTop, F n x ∈ Set.Icc (-bound x) (bound x) := by
      refine Filter.Eventually.of_forall ?_
      intro n
      exact abs_le.mp (h_bound n x)
    have hf_mem : f x ∈ Set.Icc (-bound x) (bound x) := h_closed.mem_of_tendsto (h_lim x) h_mem
    exact abs_le.mpr hf_mem
  have hF_int : ∀ n, Integrable (F n) μ := by
    intro n
    refine ⟨hF_meas n, ?_⟩
    refine hasFiniteIntegral_of_ne_top ?_
    refine ne_top_of_le_ne_top (h_bound_int.lintegral_ne_top_of_nonneg h_bound_nonneg) ?_
    exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (h_bound n x)
  have hf_int : Integrable f μ := by
    refine ⟨hf_meas, ?_⟩
    refine hasFiniteIntegral_of_ne_top ?_
    refine ne_top_of_le_ne_top (h_bound_int.lintegral_ne_top_of_nonneg h_bound_nonneg) ?_
    exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (h_abs_f_le x)
  have h_pos_lim : ∀ x, Tendsto (fun n ↦ posPart (F n) x) atTop (nhds (posPart f x)) := by
    intro x
    simpa [posPart] using ((ENNReal.continuous_ofReal.tendsto (f x)).comp (h_lim x))
  have h_neg_lim : ∀ x, Tendsto (fun n ↦ negPart (F n) x) atTop (nhds (negPart f x)) := by
    intro x
    simpa [negPart] using
      (((ENNReal.continuous_ofReal.comp continuous_neg).tendsto (f x)).comp (h_lim x))
  have h_pos_tendsto :
      Tendsto (fun n ↦ ∫⁻ x, posPart (F n) x ∂μ) atTop (nhds (∫⁻ x, posPart f x ∂μ)) := by
    exact tendsto_lintegral_of_dominated_convergence
      (fun x ↦ ENNReal.ofReal (bound x))
      (fun n ↦ measurable_posPart (hF_meas n))
      (fun n ↦ ae_of_all _ fun x ↦
        le_trans (posPart_le_abs (f := F n) x) (ENNReal.ofReal_le_ofReal (h_bound n x)))
      (h_bound_int.lintegral_ne_top_of_nonneg h_bound_nonneg)
      (ae_of_all _ h_pos_lim)
  have h_neg_tendsto :
      Tendsto (fun n ↦ ∫⁻ x, negPart (F n) x ∂μ) atTop (nhds (∫⁻ x, negPart f x ∂μ)) := by
    exact tendsto_lintegral_of_dominated_convergence
      (fun x ↦ ENNReal.ofReal (bound x))
      (fun n ↦ measurable_negPart (hF_meas n))
      (fun n ↦ ae_of_all _ fun x ↦
        le_trans (negPart_le_abs (f := F n) x) (ENNReal.ofReal_le_ofReal (h_bound n x)))
      (h_bound_int.lintegral_ne_top_of_nonneg h_bound_nonneg)
      (ae_of_all _ h_neg_lim)
  have h_pos_toReal :
      Tendsto (fun n ↦ (∫⁻ x, posPart (F n) x ∂μ).toReal) atTop
        (nhds ((∫⁻ x, posPart f x ∂μ).toReal)) := by
    exact (ENNReal.tendsto_toReal hf_int.posPart_ne_top).comp h_pos_tendsto
  have h_neg_toReal :
      Tendsto (fun n ↦ (∫⁻ x, negPart (F n) x ∂μ).toReal) atTop
        (nhds ((∫⁻ x, negPart f x ∂μ).toReal)) := by
    exact (ENNReal.tendsto_toReal hf_int.negPart_ne_top).comp h_neg_tendsto
  have hF_integral :
      (fun n ↦ ∫ x, F n x ∂μ) =
        (fun n ↦ (∫⁻ x, posPart (F n) x ∂μ).toReal - (∫⁻ x, negPart (F n) x ∂μ).toReal) := by
    funext n
    exact integral_eq_lintegral_posPart_sub_lintegral_negPart (hF_int n)
  rw [hF_integral, integral_eq_lintegral_posPart_sub_lintegral_negPart hf_int]
  exact h_pos_toReal.sub h_neg_toReal

end MTI
