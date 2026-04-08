import MeasureTheory.Lean.Prod
import MeasureTheory.Lean.Integral

noncomputable section

open MeasureTheory Set Function ENNReal MeasureTheory.Measure

namespace MTI

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y}

theorem Integrable.swap [SFinite μ] [SFinite ν] {f : X × Y → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    Integrable (fun z : Y × X ↦ f z.swap) (ν.prod μ) := by
  refine ⟨hf.measurable.comp measurable_swap, ?_⟩
  refine hasFiniteIntegral_of_ne_top ?_
  rw [show (∫⁻ z : Y × X, ENNReal.ofReal |f z.swap| ∂(ν.prod μ))
      = ∫⁻ z : X × Y, ENNReal.ofReal |f z| ∂(μ.prod ν) by
        simpa using
          (lintegral_prod_swap (μ := μ) (ν := ν) (fun z : X × Y ↦ ENNReal.ofReal |f z|))]
  exact hf.abs_ne_top

/-- Tonelli-Fubini for nonnegative real-valued functions. -/
theorem integral_prod_of_nonneg [SFinite ν] {f : X × Y → ℝ}
    (hf_meas : Measurable f) (hf_nonneg : ∀ z, 0 ≤ f z)
    (hf_fin : ∫⁻ z, ENNReal.ofReal (f z) ∂(μ.prod ν) ≠ ∞) :
    ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  let F : X → ℝ≥0∞ := fun x ↦ ∫⁻ y, ENNReal.ofReal (f (x, y)) ∂ν
  have hf_ennreal : Measurable fun z ↦ ENNReal.ofReal (f z) := hf_meas.ennreal_ofReal
  have hF_meas : Measurable F := by
    simpa [F] using hf_ennreal.lintegral_prod_right'
  have hF_eq :
      ∫⁻ x, F x ∂μ = ∫⁻ z, ENNReal.ofReal (f z) ∂(μ.prod ν) := by
    simpa [F] using (lintegral_prod hf_meas.ennreal_ofReal).symm
  have hF_fin : ∫⁻ x, F x ∂μ ≠ ∞ := by
    rw [hF_eq]
    exact hf_fin
  have hF_fin_ae : ∀ᵐ x ∂μ, F x < ∞ := ae_lt_top hF_meas hF_fin
  have hF_toReal_meas : Measurable fun x ↦ (F x).toReal := by
    simpa using hF_meas.ennreal_toReal
  have hsec_meas : ∀ x, Measurable fun y ↦ f (x, y) := by
    intro x
    simpa using hf_meas.comp (measurable_prodMk_left (x := x))
  calc
    ∫ z, f z ∂(μ.prod ν)
      = (∫⁻ z, ENNReal.ofReal (f z) ∂(μ.prod ν)).toReal :=
          integral_eq_lintegral_of_nonneg hf_meas hf_nonneg
    _ = (∫⁻ x, F x ∂μ).toReal := by rw [hF_eq.symm]
    _ = (∫⁻ x, ENNReal.ofReal ((F x).toReal) ∂μ).toReal := by
          congr 1
          refine lintegral_congr_ae ?_
          exact hF_fin_ae.mono fun x hx ↦ by
            simp [F, ENNReal.ofReal_toReal hx.ne]
    _ = ∫ x, (F x).toReal ∂μ := by
          symm
          exact integral_eq_lintegral_of_nonneg hF_toReal_meas fun x ↦ ENNReal.toReal_nonneg
    _ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
          congr 1
          funext x
          symm
          exact integral_eq_lintegral_of_nonneg (hsec_meas x) fun y ↦ hf_nonneg (x, y)

/-- Fubini's theorem for the positive part of an integrable function. -/
theorem integral_prod_posPart [SFinite ν] {f : X × Y → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    ∫ p, (posPart f p).toReal ∂(μ.prod ν)
      = ∫ x, ∫ y, (posPart f (x, y)).toReal ∂ν ∂μ := by
  have hmeas : Measurable fun z ↦ (posPart f z).toReal := by
    simpa using (measurable_posPart hf.measurable).ennreal_toReal
  have hnonneg : ∀ z, 0 ≤ (posPart f z).toReal := by
    intro z
    simp
  have hfin : ∫⁻ z, ENNReal.ofReal ((posPart f z).toReal) ∂(μ.prod ν) ≠ ∞ := by
    simpa [posPart] using hf.hasFiniteIntegral.pos_ne_top
  simpa using integral_prod_of_nonneg hmeas hnonneg hfin

/-- Fubini's theorem for the negative part of an integrable function. -/
theorem integral_prod_negPart [SFinite ν] {f : X × Y → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    ∫ p, (negPart f p).toReal ∂(μ.prod ν)
      = ∫ x, ∫ y, (negPart f (x, y)).toReal ∂ν ∂μ := by
  have hmeas : Measurable fun z ↦ (negPart f z).toReal := by
    simpa using (measurable_negPart hf.measurable).ennreal_toReal
  have hnonneg : ∀ z, 0 ≤ (negPart f z).toReal := by
    intro z
    simp
  have hfin : ∫⁻ z, ENNReal.ofReal ((negPart f z).toReal) ∂(μ.prod ν) ≠ ∞ := by
    simpa [negPart] using hf.hasFiniteIntegral.neg_ne_top
  simpa using integral_prod_of_nonneg hmeas hnonneg hfin

/-- The integral of the positive part of a section is the lower integral written in real form. -/
theorem integral_section_posPart_eq_toReal_lintegral [SFinite ν] {f : X × Y → ℝ}
    (hf_meas : Measurable f) (x : X) :
    ∫ y, (posPart f (x, y)).toReal ∂ν = (∫⁻ y, posPart f (x, y) ∂ν).toReal := by
  have hsec_meas : Measurable fun y ↦ (posPart f (x, y)).toReal := by
    simpa using
      (measurable_posPart (hf_meas.comp (measurable_prodMk_left (x := x)))).ennreal_toReal
  rw [integral_eq_lintegral_of_nonneg (μ := ν) hsec_meas
    (f := fun y ↦ (posPart f (x, y)).toReal)]
  · congr 1
    refine lintegral_congr fun y ↦ ?_
    simp [posPart]
  · intro y
    simp

/-- The integral of the negative part of a section is the lower integral written in real form. -/
theorem integral_section_negPart_eq_toReal_lintegral [SFinite ν] {f : X × Y → ℝ}
    (hf_meas : Measurable f) (x : X) :
    ∫ y, (negPart f (x, y)).toReal ∂ν = (∫⁻ y, negPart f (x, y) ∂ν).toReal := by
  have hsec_meas : Measurable fun y ↦ (negPart f (x, y)).toReal := by
    simpa using
      (measurable_negPart (hf_meas.comp (measurable_prodMk_left (x := x)))).ennreal_toReal
  rw [integral_eq_lintegral_of_nonneg (μ := ν) hsec_meas
    (f := fun y ↦ (negPart f (x, y)).toReal)]
  · congr 1
    refine lintegral_congr fun y ↦ ?_
    simp [negPart]
  · intro y
    simp

/-- Almost every section of an integrable function is integrable. -/
theorem ae_integrable_sections [SFinite ν] {f : X × Y → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ f (x, y)) ν := by
  let Gpos : X → ℝ≥0∞ := fun x ↦ ∫⁻ y, posPart f (x, y) ∂ν
  let Gneg : X → ℝ≥0∞ := fun x ↦ ∫⁻ y, negPart f (x, y) ∂ν
  have hpos_meas : Measurable (posPart f) := measurable_posPart hf.measurable
  have hneg_meas : Measurable (negPart f) := measurable_negPart hf.measurable
  have hGpos_meas : Measurable Gpos := by
    simpa [Gpos] using hpos_meas.lintegral_prod_right'
  have hGneg_meas : Measurable Gneg := by
    simpa [Gneg] using hneg_meas.lintegral_prod_right'
  have hGpos_eq :
      ∫⁻ x, Gpos x ∂μ = ∫⁻ z, posPart f z ∂(μ.prod ν) := by
    simpa [Gpos] using (lintegral_prod hpos_meas).symm
  have hGneg_eq :
      ∫⁻ x, Gneg x ∂μ = ∫⁻ z, negPart f z ∂(μ.prod ν) := by
    simpa [Gneg] using (lintegral_prod hneg_meas).symm
  have hGpos_fin_ae : ∀ᵐ x ∂μ, Gpos x < ∞ := by
    apply ae_lt_top hGpos_meas
    rw [hGpos_eq]
    exact hf.hasFiniteIntegral.pos_ne_top
  have hGneg_fin_ae : ∀ᵐ x ∂μ, Gneg x < ∞ := by
    apply ae_lt_top hGneg_meas
    rw [hGneg_eq]
    exact hf.hasFiniteIntegral.neg_ne_top
  filter_upwards [hGpos_fin_ae, hGneg_fin_ae] with x hxpos hxneg
  have hsec_meas : Measurable fun y ↦ f (x, y) := by
    simpa using hf.measurable.comp (measurable_prodMk_left (x := x))
  have hsec_pos_meas : Measurable fun y ↦ posPart (fun y ↦ f (x, y)) y := by
    exact measurable_posPart hsec_meas
  have hsec_pos_fin : ∫⁻ y, posPart (fun y ↦ f (x, y)) y ∂ν ≠ ∞ := by
    simpa [Gpos, posPart] using hxpos.ne
  have hsec_neg_fin : ∫⁻ y, negPart (fun y ↦ f (x, y)) y ∂ν ≠ ∞ := by
    simpa [Gneg, negPart] using hxneg.ne
  refine ⟨hsec_meas, ?_⟩
  refine hasFiniteIntegral_of_ne_top ?_
  rw [show (∫⁻ y, ENNReal.ofReal |f (x, y)| ∂ν)
      = ∫⁻ y, (posPart (fun y ↦ f (x, y)) y + negPart (fun y ↦ f (x, y)) y) ∂ν by
        apply lintegral_congr
        intro y
        symm
        exact posPart_add_negPart_eq_abs (f := fun y ↦ f (x, y)) y]
  rw [lintegral_add_left hsec_pos_meas]
  exact add_ne_top.mpr ⟨hsec_pos_fin, hsec_neg_fin⟩

/-- The positive-part section integral is measurable in the outer variable. -/
theorem measurable_integral_section_posPart [SFinite ν] {f : X × Y → ℝ}
    (hf_meas : Measurable f) :
    Measurable fun x ↦ ∫ y, (posPart f (x, y)).toReal ∂ν := by
  let Gpos : X → ℝ≥0∞ := fun x ↦ ∫⁻ y, posPart f (x, y) ∂ν
  have hpos_meas : Measurable (posPart f) := measurable_posPart hf_meas
  have hGpos_meas : Measurable Gpos := by
    simpa [Gpos] using hpos_meas.lintegral_prod_right'
  have hEq :
      (fun x ↦ ∫ y, (posPart f (x, y)).toReal ∂ν) = fun x ↦ (Gpos x).toReal := by
    funext x
    simpa [Gpos] using integral_section_posPart_eq_toReal_lintegral hf_meas x
  rw [hEq]
  simpa using hGpos_meas.ennreal_toReal

/-- The negative-part section integral is measurable in the outer variable. -/
theorem measurable_integral_section_negPart [SFinite ν] {f : X × Y → ℝ}
    (hf_meas : Measurable f) :
    Measurable fun x ↦ ∫ y, (negPart f (x, y)).toReal ∂ν := by
  let Gneg : X → ℝ≥0∞ := fun x ↦ ∫⁻ y, negPart f (x, y) ∂ν
  have hneg_meas : Measurable (negPart f) := measurable_negPart hf_meas
  have hGneg_meas : Measurable Gneg := by
    simpa [Gneg] using hneg_meas.lintegral_prod_right'
  have hEq :
      (fun x ↦ ∫ y, (negPart f (x, y)).toReal ∂ν) = fun x ↦ (Gneg x).toReal := by
    funext x
    simpa [Gneg] using integral_section_negPart_eq_toReal_lintegral hf_meas x
  rw [hEq]
  simpa using hGneg_meas.ennreal_toReal

/-- The positive-part section integrals have finite lower integral. -/
theorem lintegral_integral_section_posPart_ne_top [SFinite ν] {f : X × Y → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    ∫⁻ x, ENNReal.ofReal (∫ y, (posPart f (x, y)).toReal ∂ν) ∂μ ≠ ∞ := by
  let Gpos : X → ℝ≥0∞ := fun x ↦ ∫⁻ y, posPart f (x, y) ∂ν
  have hpos_meas : Measurable (posPart f) := measurable_posPart hf.measurable
  have hGpos_meas : Measurable Gpos := by
    simpa [Gpos] using hpos_meas.lintegral_prod_right'
  have hGpos_eq :
      ∫⁻ x, Gpos x ∂μ = ∫⁻ z, posPart f z ∂(μ.prod ν) := by
    simpa [Gpos] using (lintegral_prod hpos_meas).symm
  have hGpos_fin : ∫⁻ x, Gpos x ∂μ ≠ ∞ := by
    rw [hGpos_eq]
    exact hf.hasFiniteIntegral.pos_ne_top
  have hGpos_fin_ae : ∀ᵐ x ∂μ, Gpos x < ∞ := ae_lt_top hGpos_meas hGpos_fin
  have hEq :
      ∫⁻ x, ENNReal.ofReal (∫ y, (posPart f (x, y)).toReal ∂ν) ∂μ = ∫⁻ x, Gpos x ∂μ := by
    refine lintegral_congr_ae ?_
    exact hGpos_fin_ae.mono fun x hx ↦ by
      change ENNReal.ofReal (∫ y, (posPart f (x, y)).toReal ∂ν) = Gpos x
      rw [integral_section_posPart_eq_toReal_lintegral hf.measurable x]
      simpa [Gpos] using (ENNReal.ofReal_toReal hx.ne)
  rw [hEq]
  exact hGpos_fin

/-- The positive-part section integrals are integrable in the outer variable. -/
theorem integrable_integral_section_posPart [SFinite ν] {f : X × Y → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x ↦ ∫ y, (posPart f (x, y)).toReal ∂ν) μ := by
  refine ⟨measurable_integral_section_posPart hf.measurable, ?_⟩
  refine hasFiniteIntegral_of_ne_top ?_
  have hEq :
      ∫⁻ x, ENNReal.ofReal |∫ y, (posPart f (x, y)).toReal ∂ν| ∂μ
        = ∫⁻ x, ENNReal.ofReal (∫ y, (posPart f (x, y)).toReal ∂ν) ∂μ := by
    refine lintegral_congr fun x ↦ ?_
    congr 1
    apply abs_of_nonneg
    rw [integral_section_posPart_eq_toReal_lintegral hf.measurable x]
    exact ENNReal.toReal_nonneg
  rw [hEq]
  exact lintegral_integral_section_posPart_ne_top hf

/-- The negative-part section integrals have finite lower integral. -/
theorem lintegral_integral_section_negPart_ne_top [SFinite ν] {f : X × Y → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    ∫⁻ x, ENNReal.ofReal (∫ y, (negPart f (x, y)).toReal ∂ν) ∂μ ≠ ∞ := by
  let Gneg : X → ℝ≥0∞ := fun x ↦ ∫⁻ y, negPart f (x, y) ∂ν
  have hneg_meas : Measurable (negPart f) := measurable_negPart hf.measurable
  have hGneg_meas : Measurable Gneg := by
    simpa [Gneg] using hneg_meas.lintegral_prod_right'
  have hGneg_eq :
      ∫⁻ x, Gneg x ∂μ = ∫⁻ z, negPart f z ∂(μ.prod ν) := by
    simpa [Gneg] using (lintegral_prod hneg_meas).symm
  have hGneg_fin : ∫⁻ x, Gneg x ∂μ ≠ ∞ := by
    rw [hGneg_eq]
    exact hf.hasFiniteIntegral.neg_ne_top
  have hGneg_fin_ae : ∀ᵐ x ∂μ, Gneg x < ∞ := ae_lt_top hGneg_meas hGneg_fin
  have hEq :
      ∫⁻ x, ENNReal.ofReal (∫ y, (negPart f (x, y)).toReal ∂ν) ∂μ = ∫⁻ x, Gneg x ∂μ := by
    refine lintegral_congr_ae ?_
    exact hGneg_fin_ae.mono fun x hx ↦ by
      change ENNReal.ofReal (∫ y, (negPart f (x, y)).toReal ∂ν) = Gneg x
      rw [integral_section_negPart_eq_toReal_lintegral hf.measurable x]
      simpa [Gneg] using (ENNReal.ofReal_toReal hx.ne)
  rw [hEq]
  exact hGneg_fin

/-- The negative-part section integrals are integrable in the outer variable. -/
theorem integrable_integral_section_negPart [SFinite ν] {f : X × Y → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    Integrable (fun x ↦ ∫ y, (negPart f (x, y)).toReal ∂ν) μ := by
  refine ⟨measurable_integral_section_negPart hf.measurable, ?_⟩
  refine hasFiniteIntegral_of_ne_top ?_
  have hEq :
      ∫⁻ x, ENNReal.ofReal |∫ y, (negPart f (x, y)).toReal ∂ν| ∂μ
        = ∫⁻ x, ENNReal.ofReal (∫ y, (negPart f (x, y)).toReal ∂ν) ∂μ := by
    refine lintegral_congr fun x ↦ ?_
    congr 1
    apply abs_of_nonneg
    rw [integral_section_negPart_eq_toReal_lintegral hf.measurable x]
    exact ENNReal.toReal_nonneg
  rw [hEq]
  apply lintegral_integral_section_negPart_ne_top hf

/-- Almost every section integral splits into the difference of the positive and negative section
integrals. -/
theorem integral_sections_eq_integral_posPart_sub_integral_negPart_ae [SFinite ν]
    {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    (fun x ↦ ∫ y, f (x, y) ∂ν) =ᵐ[μ]
      fun x ↦ ∫ y, (posPart f (x, y)).toReal ∂ν - ∫ y, (negPart f (x, y)).toReal ∂ν := by
  filter_upwards [ae_integrable_sections hf] with x hx
  apply integral_eq_integral_posPart_sub_integral_negPart hx

/-- Fubini's theorem for real-valued functions. -/
theorem integral_prod [SFinite ν] {f : X × Y → ℝ} (hf : Integrable f (μ.prod ν)) :
    ∫ p, f p ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  calc
    ∫ p, f p ∂(μ.prod ν)
      = ∫ p, (posPart f p).toReal ∂(μ.prod ν) - ∫ p, (negPart f p).toReal ∂(μ.prod ν) := by
          apply integral_eq_integral_posPart_sub_integral_negPart hf
    _ = ∫ x, ∫ y, (posPart f (x, y)).toReal ∂ν ∂μ
        - ∫ x, ∫ y, (negPart f (x, y)).toReal ∂ν ∂μ := by
          rw [integral_prod_posPart hf, integral_prod_negPart hf]
    _ = ∫ x,
          (∫ y, (posPart f (x, y)).toReal ∂ν - ∫ y, (negPart f (x, y)).toReal ∂ν) ∂μ := by
          symm
          apply integral_sub_eq_integral_sub
            (integrable_integral_section_posPart hf) (integrable_integral_section_negPart hf)
    _ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
          apply integral_congr_ae
          apply
            (integral_sections_eq_integral_posPart_sub_integral_negPart_ae hf).symm

theorem integral_prod_swap [SFinite μ] [SFinite ν] (f : X × Y → ℝ)
    (hf : Measurable f) :
    ∫ z, f z.swap ∂(ν.prod μ) = ∫ z, f z ∂(μ.prod ν) :=
  calc
    ∫ z, f z.swap ∂(ν.prod μ) = ∫ z, f z ∂(MeasureTheory.Measure.map Prod.swap (ν.prod μ)) :=
      (integral_map hf measurable_swap).symm
    _ = ∫ z, f z ∂(μ.prod ν) := by
      rw [prod_swap]

theorem integral_prod_swap' [SFinite μ] [SFinite ν] {f : X × Y → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    ∫ x, ∫ y, f (x, y) ∂ν ∂μ = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
  calc
    ∫ x, ∫ y, f (x, y) ∂ν ∂μ = ∫ z, f z ∂(μ.prod ν) := by
      apply (integral_prod hf).symm
    _ = ∫ z, f z.swap ∂(ν.prod μ) := by
      apply (integral_prod_swap f hf.measurable).symm
    _ = ∫ y, ∫ x, f (y, x).swap ∂μ ∂ν := by
      apply integral_prod hf.swap
    _ = ∫ y, ∫ x, f (x, y) ∂μ ∂ν := by
      simp only [Prod.swap_prod_mk]

end MTI
