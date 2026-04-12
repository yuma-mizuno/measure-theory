import Mathlib.MeasureTheory.Integral.Lebesgue.Add

noncomputable section

open ENNReal Set Filter
open MeasureTheory

namespace MTI

variable {X Y Z : Type*}

variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def Measure.dirac (x : X) : Measure X :=
  Measure.ofMeasurable (fun A _ ↦ indicator A (fun _ ↦ 1) x) (by simp) <| by
    intro A hA hAd
    simp only
    by_cases hx : x ∈ (⋃ i, A i)
    · rw [indicator_of_mem hx]
      simp only [mem_iUnion] at hx
      have ⟨i, hi⟩ := hx
      have : ∑' (i : ℕ), (A i).indicator (fun x ↦ (1 : ℝ≥0∞)) x =
          (A i).indicator (fun x ↦ (1 : ℝ≥0∞)) x +
            ∑' k : ℕ, if k = i then 0 else (A k).indicator (fun x ↦ (1 : ℝ≥0∞)) x := by
        convert tsum_eq_add_tsum_ite (f := fun i ↦ (A i).indicator (fun x ↦ (1 : ℝ≥0∞)) x) i
      rw [this]
      rw [indicator_of_mem hi]
      suffices (∑' k : ℕ, if k = i then 0 else (A k).indicator (fun x ↦ (1 : ℝ≥0∞)) x) = 0 by
        rw [this]
        simp
      refine ENNReal.tsum_eq_zero.mpr ?_
      intro k
      simp only [ite_eq_left_iff, indicator_apply_eq_zero, one_ne_zero, imp_false]
      intro hik hAk
      have hx : x ∈ A i ∩ A k := by
        exact mem_inter hi hAk
      apply hAd hik _ _ hx
      · simp
      · simp
    · rw [indicator_of_notMem hx]
      simp only [mem_iUnion, not_exists] at hx
      symm
      refine ENNReal.tsum_eq_zero.mpr ?_
      intro i
      rw [indicator_of_notMem (hx i)]

@[simp]
theorem Measure.dirac_apply (x : X) (A : Set X) (hA : MeasurableSet A) :
    Measure.dirac x A = indicator A (fun _ ↦ 1) x := by
  rw [Measure.dirac, Measure.ofMeasurable_apply _ hA]

theorem ae_eq_dirac {a : X} {f : X → ℝ≥0∞} (hf : Measurable f) :
    f =ᵐ[Measure.dirac a] Function.const X (f a) := by
  change ∀ᵐ x ∂(Measure.dirac a), f x = f a
  suffices MeasurableSet { x | f x = f a } from by
    rw [ae_iff]
    calc
      (Measure.dirac a) {x | ¬f x = f a} = (Measure.dirac a) {x | f x = f a}ᶜ := by grind
      _ = 0 := by
        rw [measure_compl this]
        · rw [Measure.dirac_apply a _ this]
          rw [Measure.dirac_apply _ _ MeasurableSet.univ]
          rw [indicator_of_mem (mem_univ _)]
          rw [indicator_of_mem (by grind)]
          rw [tsub_self]
        · rw [Measure.dirac_apply a _ this]
          simp
  refine measurableSet_eq_fun hf measurable_const

theorem lintegral_dirac (a : X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂Measure.dirac a = f a :=
  calc
    ∫⁻ x, f x ∂Measure.dirac a = ∫⁻ x, f a ∂Measure.dirac a :=
      lintegral_congr_ae (ae_eq_dirac hf)
    _ = (SimpleFunc.const _ (f a)).lintegral (Measure.dirac a) := by
      rw [← SimpleFunc.lintegral_eq_lintegral]
      apply lintegral_congr
      intro x
      simp
    _ = ∑ x ∈ (SimpleFunc.const X (f a)).range,
        x * (Measure.dirac a) ((SimpleFunc.const X (f a)) ⁻¹' {x}) := by
      rw [SimpleFunc.lintegral]
    _ = ∑ x ∈ (SimpleFunc.const X (f a)).range,
        x * indicator ((SimpleFunc.const X (f a)) ⁻¹' {x}) (fun _ ↦ 1) a := by
      congr 1
      ext x
      congr 1
      apply Measure.dirac_apply a
      exact SimpleFunc.measurableSet_fiber (SimpleFunc.const X (f a)) x
    _ = f a * ((Measure.dirac a) univ) := by
      cases isEmpty_or_nonempty X
      · simp [(Measure.dirac a).eq_zero_of_isEmpty]
      · simp
    _ = f a := by simp

inductive Measure.MeasurableGen (X : Type*) [MeasurableSpace X] : Set (Set (Measure X))
  | mk (A : Set X) (hs : MeasurableSet A) (B : Set ℝ≥0∞) (hB : MeasurableSet B) :
      Measure.MeasurableGen X ({μ | μ A ∈ B})

instance Measure.instMeasurableSpace : MeasurableSpace (Measure X) :=
  MeasurableSpace.generateFrom (Measure.MeasurableGen X)

theorem Measure.measurable_coe {A : Set X} (hA : MeasurableSet A) :
    Measurable fun μ : Measure X ↦ μ A :=
  fun {B} hB ↦ MeasurableSpace.measurableSet_generateFrom (MeasurableGen.mk A hA B hB)

@[fun_prop]
theorem Measure.measurable_lintegral {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure X ↦ ∫⁻ x, f x ∂μ := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n ↦ Finset.measurable_fun_sum _ fun i _ ↦ ?_
  refine Measurable.const_mul ?_ _
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)

theorem measurable_of_measurable_coe (μ : X → Measure Y)
    (h : ∀ (A : Set Y), MeasurableSet A → Measurable fun x ↦ μ x A) : Measurable μ := by
  intro A hA
  induction hA with
  | basic S hS =>
    obtain ⟨A, hA, B, hB⟩ := hS
    simp only [preimage_setOf_eq, measurableSet_setOf]
    exact measurableSet_setOf.mp (h A hA hB)
  | empty => simp
  | compl A hA ih =>
    rw [@preimage_compl]
    apply ih.compl
  | iUnion A hAd ihA =>
    rw [@preimage_iUnion]
    apply MeasurableSet.iUnion ihA

theorem Measure.dirac_measurable : Measurable (Measure.dirac : X → Measure X) := by
  intro A hA
  induction hA with
  | basic A hA =>
    rcases hA with ⟨A, hA, B, hB⟩
    have : MeasurableSet ((indicator A (fun _ ↦ (1 : ℝ≥0∞))) ⁻¹' B)  :=
      measurable_const.indicator hA hB
    apply MeasurableSet.congr this
    simp only [preimage_setOf_eq, dirac_apply _ _ hA]
    grind
  | empty => simp
  | compl A hA ih =>
    simp only [preimage_compl]
    apply ih.compl
  | iUnion A hA ih =>
    simp only [preimage_iUnion]
    apply MeasurableSet.iUnion ih

open Classical in
def Measure.bind (f : X → Measure Y) (μ : Measure X) : Measure Y :=
  if hf : Measurable f then
    Measure.ofMeasurable (fun A _ ↦ ∫⁻ x, f x A ∂μ) (by simp) <| fun A hA hAd ↦
      calc
      ∫⁻ (x : X), (f x) (⋃ i, A i) ∂μ
      _ = ∫⁻ (x : X), ∑' (i : ℕ), (f x) (A i) ∂μ :=
        lintegral_congr (fun x ↦ measure_iUnion hAd hA)
      _ = ∑' (i : ℕ), ∫⁻ (x : X), (f x) (A i) ∂μ :=
        lintegral_tsum (fun n ↦ ((measurable_coe (hA n)).comp hf).aemeasurable)
  else 0

@[simp]
theorem Measure.bind_apply (f : X → Measure Y) (hf : Measurable f) (μ : Measure X) (A : Set Y)
    (hA : MeasurableSet A) :
    bind f μ A = ∫⁻ x, f x A ∂μ := by
  rw [bind, dif_pos hf]
  apply Measure.ofMeasurable_apply _ hA

theorem Measure.dirac_lintegral (f : X → ℝ≥0∞) (hf : Measurable f) (x : X) :
    ∫⁻ y, f y ∂(dirac x) = f x := by
  have : f =ᶠ[ae (dirac x)] Function.const X (f x) := by
    have : ∀ᵐ y ∂(dirac x), y ∈ { y | f y = f x } := by
      rw [eventually_mem_set, mem_ae_iff, dirac_apply]
      · simp
      · apply MeasurableSet.compl
        suffices MeasurableSet (f ⁻¹' {f x}) from this
        apply hf (measurableSet_singleton (f x))
    filter_upwards [this] with y hy using by simpa using hy
  apply (lintegral_congr_ae this).trans (by simp)

theorem Measure.dirac_bind (f : X → Measure Y) (hf : Measurable f) :
    bind f ∘ dirac = f := by
  ext x A hA
  simp only [Function.comp_apply, bind_apply f hf (dirac x) A hA]
  exact dirac_lintegral (fun y ↦ f y A) ((measurable_coe hA).comp hf) x

theorem Measure.bind_dirac (μ : Measure X) :
    bind dirac μ = μ := by
  ext A hA
  simp only [bind_apply dirac dirac_measurable μ A hA]
  simp only [dirac_apply _ A hA]
  rw [lintegral_indicator hA fun x ↦ 1]
  rw [@setLIntegral_one]

theorem lintegral_bind {m : Measure X} {μ : X → Measure Y} {f : Y → ℝ≥0∞} (hμ : Measurable μ)
    (hf : Measurable f) : ∫⁻ y, f y ∂Measure.bind μ m = ∫⁻ x, ∫⁻ y, f y ∂μ x ∂m := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  dsimp only [SimpleFunc.lintegral]
  calc
    ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        a * (Measure.bind μ m) ((SimpleFunc.eapprox f n) ⁻¹' {a})
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        a * (∫⁻ x, μ x ((SimpleFunc.eapprox f n) ⁻¹' {a}) ∂m) := by
      congr 1
      ext n
      congr 1
      ext a
      congr 1
      rw [Measure.bind_apply μ hμ m]
      exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox f n) a
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        (∫⁻ x, a * μ x ((SimpleFunc.eapprox f n) ⁻¹' {a}) ∂m) := by
      congr 1
      ext n
      congr 1
      ext a
      apply (lintegral_const_mul _ _).symm
      have : (fun x ↦ (μ x) ((SimpleFunc.eapprox f n) ⁻¹' {a})) =
          ((fun ν : Measure Y ↦ ν ((SimpleFunc.eapprox f n) ⁻¹' {a})) ∘ μ) := by
        rfl
      rw [this]
      apply Measurable.comp _ hμ
      refine Measure.measurable_coe ?_
      exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox f n) a
    _ = ⨆ n, (∫⁻ x, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        a * μ x ((SimpleFunc.eapprox f n) ⁻¹' {a}) ∂m) := by
      congr 1
      ext n
      refine Eq.symm (lintegral_finset_sum' (SimpleFunc.eapprox f n).range ?_)
      intro a ha
      apply Measurable.aemeasurable
      refine Measurable.mul ?_ ?_
      · exact measurable_const
      · have : (fun x ↦ (μ x) ((SimpleFunc.eapprox f n) ⁻¹' {a})) =
            ((fun ν : Measure Y ↦ ν ((SimpleFunc.eapprox f n) ⁻¹' {a})) ∘ μ) := by
          rfl
        rw [this]
        apply Measurable.comp _ hμ
        refine Measure.measurable_coe ?_
        exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox f n) a
    _ = (∫⁻ x, ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        a * μ x ((SimpleFunc.eapprox f n) ⁻¹' {a}) ∂m) := by
      refine Eq.symm (lintegral_iSup' ?_ ?_)
      · intro n
        apply Measurable.aemeasurable
        refine Finset.measurable_fun_sum (SimpleFunc.eapprox f n).range ?_
        intro a ha
        refine Measurable.const_mul ?_ a
        have : (fun x ↦ (μ x) ((SimpleFunc.eapprox f n) ⁻¹' {a})) =
            ((fun ν : Measure Y ↦ ν ((SimpleFunc.eapprox f n) ⁻¹' {a})) ∘ μ) := by
          rfl
        rw [this]
        apply Measurable.comp _ hμ
        refine Measure.measurable_coe ?_
        exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox f n) a
      · filter_upwards with a i j hij
        simp only
        rw [← SimpleFunc.lintegral]
        rw [← SimpleFunc.lintegral]
        apply SimpleFunc.lintegral_mono _ (le_of_eq rfl)
        apply SimpleFunc.monotone_eapprox f hij
    _ = ∫⁻ (a : X), ∫⁻ (x : Y), f x ∂μ a ∂m := by
      apply lintegral_congr
      intro x
      simp only [← SimpleFunc.iSup_eapprox_apply hf]
      rw [lintegral_iSup]
      · congr 1
        ext n
        rw [SimpleFunc.lintegral_eq_lintegral]
        rw [SimpleFunc.lintegral]
      · intro n
        exact SimpleFunc.measurable (SimpleFunc.eapprox f n)
      · intro i j hij
        dsimp only
        gcongr

theorem Measure.bind_measurable (f : X → Measure Y) (hf : Measurable f) :
    Measurable (Measure.bind f) := by
  refine measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp only [Measure.bind_apply f hf _ A hA]
  apply measurable_lintegral
  exact (Measure.measurable_coe hA).comp hf

theorem Measure.bind_assoc
    (ν : X → Measure Y) (hν : Measurable ν)
    (ℓ : Y → Measure Z) (hℓ : Measurable ℓ) :
    bind ℓ ∘ bind ν =
      bind (bind ℓ ∘ ν) := by
  ext μ A hA
  dsimp only [Function.comp_apply]
  rw [Measure.bind_apply ℓ hℓ (Measure.bind ν μ) A hA]
  rw [Measure.bind_apply _ ((bind_measurable ℓ hℓ).comp hν) _ _ hA]
  rw [lintegral_bind hν]
  · apply lintegral_congr (fun x ↦ (Measure.bind_apply ℓ hℓ (ν x) A hA).symm)
  · apply (measurable_coe hA).comp hℓ

end MTI
