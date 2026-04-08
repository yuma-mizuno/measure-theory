import MeasureTheory.Lean.Dynkin
import MeasureTheory.Lean.MathlibAliases

noncomputable section

open MeasureTheory Set Function ENNReal MeasurableSpace MeasureTheory.Measure

namespace MTI

variable {X Y Z : Type*}

section Prod

variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {μ : Measure X} {ν : Measure Y}

inductive GenProd (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] : Set (Set (X × Y)) where
  | basic {A : Set X} (hA : MeasurableSet A) {B : Set Y} (hB : MeasurableSet B) :
      GenProd X Y (A ×ˢ B)

instance instMeasurableSpaceProd : MeasurableSpace (X × Y) :=
  generateFrom (GenProd X Y)

@[measurability]
theorem MeasurableSet.sProd {A : Set X} (hA : MeasurableSet A) {B : Set Y} (hB : MeasurableSet B) :
    MeasurableSet (A ×ˢ B) :=
  measurableSet_generateFrom (GenProd.basic hA hB)

@[measurability]
theorem measurable_fst : Measurable (Prod.fst : X × Y → X) := by
  intro A hA
  apply measurableSet_generateFrom
  rw [← @prod_univ]
  apply GenProd.basic hA MeasurableSet.univ

@[measurability]
theorem measurable_snd : Measurable (Prod.snd : X × Y → Y) := by
  intro B hB
  apply measurableSet_generateFrom
  rw [← @univ_prod]
  apply GenProd.basic MeasurableSet.univ hB

@[measurability]
theorem Measurable.prod {f : X → Y × Z}
    (hf₁ : Measurable fun a => (f a).1) (hf₂ : Measurable fun a => (f a).2) :
    Measurable f := by
  intro A hA
  induction hA using GenerateMeasurable.rec with
  | basic A hA =>
    obtain @⟨A₁, hA₁, A₂, hA₂⟩ := hA
    measurability
  | empty => measurability
  | compl A _ ih => measurability
  | iUnion A _ ihA => measurability

@[measurability]
theorem measurable_swap : Measurable (Prod.swap : X × Y → Y × X) := by
  exact Measurable.prod measurable_snd measurable_fst

@[measurability]
theorem measurable_prodMk_left {x : X} :
    Measurable (Prod.mk x : Y → X × Y) := by
  measurability

@[measurability]
theorem measurable_prodMk_right {y : Y} :
    Measurable (fun x ↦ Prod.mk x y : X → X × Y) := by
  measurability

variable (X Y) in
theorem isPiSystem_genProd ⦃A B⦄ (hA : GenProd X Y A) (hB : GenProd X Y B) :
    GenProd X Y (A ∩ B) := by
  obtain @⟨A₁, hA₁, A₂, hA₂⟩ := hA
  obtain @⟨B₁, hB₁, B₂, hB₂⟩ := hB
  rw [prod_inter_prod]
  exact GenProd.basic (hA₁.inter hB₁) (hA₂.inter hB₂)

theorem measurable_measure_prodMk_left_finite [IsFiniteMeasure ν] {A : Set (X × Y)}
    (hA : MeasurableSet A) : Measurable fun x ↦ ν (Prod.mk x ⁻¹' A) := by
  induction A, hA using MTI.induction_on_inter rfl (isPiSystem_genProd X Y) with
  | empty => simp
  | basic A hA =>
    obtain @⟨A, hA, B, -⟩ := hA
    classical
    simp only [mk_preimage_prod_right_eq_if, measure_if]
    refine measurable_const.indicator hA
  | compl A hA ihA =>
    simp_rw [preimage_compl, measure_compl (measurable_prodMk_left hA) (measure_ne_top ν _)]
    exact ihA.const_sub _
  | iUnion A hAd hAm ih =>
    have : ∀ (x : X), ν (Prod.mk x ⁻¹' ⋃ i, A i) = ∑' i, ν (Prod.mk x ⁻¹' A i) := by
      intro x
      rw [preimage_iUnion, measure_iUnion _ (fun i ↦ measurable_prodMk_left (hAm i))]
      exact hAd.mono fun _ _ ↦ .preimage _
    simpa only [this] using Measurable.ennreal_tsum ih

@[measurability]
theorem measurable_measure_prodMk_left [SFinite ν]
    {A : Set (X × Y)}
    (hA : MeasurableSet A) : Measurable fun x ↦ ν (Prod.mk x ⁻¹' A) := by
  rw [← sum_sfiniteSeq ν]
  simp_rw [Measure.sum_apply _ (measurable_prodMk_left hA)]
  exact Measurable.ennreal_tsum (fun i ↦ measurable_measure_prodMk_left_finite hA)

/-- The lower Lebesgue integral on the fibers of a product is measurable. -/
@[fun_prop, measurability]
theorem Measurable.lintegral_prod_right' [SFinite ν] :
    ∀ {f : X × Y → ℝ≥0∞}, Measurable f → Measurable fun x ↦ ∫⁻ y, f (x, y) ∂ν := by
  have m := @measurable_prodMk_left X Y _ _
  refine Measurable.ennreal_induction
    (motive := fun f ↦ Measurable fun x : X ↦ ∫⁻ y, f (x, y) ∂ν) ?_ ?_ ?_
  · intro c A hA
    simp only [← indicator_comp_right]
    suffices Measurable fun x ↦ c * ν (Prod.mk x ⁻¹' A) by
      simpa [lintegral_indicator (m hA)] using this
    exact (measurable_measure_prodMk_left hA).const_mul _
  · rintro f g - hf hg h2f h2g
    have hadd :
        (fun x ↦ ∫⁻ y, (f + g) (x, y) ∂ν) =
          fun x ↦ ∫⁻ y, f (x, y) ∂ν + ∫⁻ y, g (x, y) ∂ν := by
      funext x
      simpa [Pi.add_apply] using
        (lintegral_add_left (hf.comp (measurable_prodMk_left (x := x))) (fun y ↦ g (x, y)))
    rw [hadd]
    exact h2f.add h2g
  · intro f hf hmono hmeas
    have hfiber : ∀ x, Monotone fun n y ↦ f n (x, y) := by
      intro x i j hij y
      exact hmono hij (x, y)
    have hiSup :
        (fun x ↦ ∫⁻ y, ⨆ n, f n (x, y) ∂ν) = fun x ↦ ⨆ n, ∫⁻ y, f n (x, y) ∂ν := by
      funext x
      exact lintegral_iSup (fun n ↦ (hf n).comp (measurable_prodMk_left (x := x))) (hfiber x)
    rw [hiSup]
    exact .iSup hmeas

@[fun_prop, measurability]
theorem Measurable.lintegral_prod_right [SFinite ν] {f : X → Y → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun x ↦ ∫⁻ y, f x y ∂ν :=
  hf.lintegral_prod_right'

def Measure.prod (μ : Measure X) (ν : Measure Y) [SFinite ν] :
    Measure (X × Y) :=
  Measure.ofMeasurable (fun A _ ↦ ∫⁻ x, ν (Prod.mk x ⁻¹' A) ∂μ) (by simp) <| fun A hA hAd ↦
    calc
    ∫⁻ (x : X), ν (Prod.mk x ⁻¹' ⋃ i, A i) ∂μ
    _ = ∫⁻ (x : X), ∑' (i : ℕ), ν (Prod.mk x ⁻¹' A i) ∂μ :=
      lintegral_congr <| by
        intro x
        rw [preimage_iUnion]
        apply
          measure_iUnion
            (fun i j hij ↦ (hAd hij).preimage (Prod.mk x))
            (fun n ↦ measurable_prodMk_left (hA n))
    _ = ∑' (i : ℕ), ∫⁻ (x : X), ν (Prod.mk x ⁻¹' A i) ∂μ := by
      rw [lintegral_tsum]
      intro n
      refine (measurable_measure_prodMk_left (hA n)).aemeasurable

theorem prod_apply [SFinite ν] {A : Set (X × Y)} (hA : MeasurableSet A) :
    μ.prod ν A = ∫⁻ x, ν (Prod.mk x ⁻¹' A) ∂μ := by
  rw [Measure.prod, Measure.ofMeasurable_apply _ hA]

theorem lintegral_prod [SFinite ν] {f : X × Y → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  dsimp only [SimpleFunc.lintegral]
  let f' : ℕ → X → SimpleFunc Y ℝ≥0∞ := fun n x ↦
    (SimpleFunc.eapprox f n).comp (Prod.mk x) measurable_prodMk_left
  have hf'_app : ∀ n x y, f' n x y = (SimpleFunc.eapprox f n) (x, y) := by
    intro n x y
    simp only [SimpleFunc.coe_comp, comp_apply, f']
  have hf' : ∀ n a, Measurable fun x ↦ ν (f' n x ⁻¹' {a}) :=
    fun n a ↦ measurable_measure_prodMk_left ((SimpleFunc.eapprox f n).measurableSet_fiber a)
  have hf'sup : ∀ x y, ⨆ n, f' n x y = f (x, y) := by
    intro x y
    simp only [SimpleFunc.coe_comp, comp_apply, f']
    rw [SimpleFunc.iSup_eapprox_apply hf (x, y)]
  have hf'_int : ∀ n x, (f' n x).lintegral ν =
      ∑ a ∈ (SimpleFunc.eapprox f n).range, a * ν ((f' n x) ⁻¹' {a}) := by
    intro n x
    refine Finset.sum_subset ?_ ?_
    · intro a ha
      simp only [SimpleFunc.mem_range, mem_range, Prod.exists] at ha ⊢
      grind
    · intro a ha ha'
      simp only [mul_eq_zero]
      right
      apply (congrArg ν _).trans measure_empty
      exact (SimpleFunc.preimage_eq_empty_iff (f' n x) a).mpr ha'
  calc
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range, a * (∫⁻ x, ν (f' n x ⁻¹' {a}) ∂μ) := by
      apply iSup_congr (fun n ↦ Finset.sum_congr rfl (fun a ha ↦ ?_))
      rw [prod_apply ((SimpleFunc.eapprox f n).measurableSet_fiber a)]
      congr
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range, ∫⁻ x, a * ν (f' n x ⁻¹' {a}) ∂μ :=
      iSup_congr <| fun n ↦ Finset.sum_congr rfl <| fun a ha ↦
        (lintegral_const_mul _ (hf' n a)).symm
    _ = ⨆ n, ∫⁻ x, (f' n x).lintegral ν ∂μ := by
      apply iSup_congr fun n ↦ ?_
      rw [← lintegral_finset_sum]
      · apply lintegral_congr fun x ↦ ?_
        rw [hf'_int]
      · intro a ha
        exact measurable_const.mul (hf' n a)
    _ = ∫⁻ x, ⨆ n, (f' n x).lintegral ν ∂μ := by
      refine (lintegral_iSup ?_ ?_).symm
      · intro n
        simp only [hf'_int n]
        exact Finset.measurable_fun_sum _ (fun a ha ↦ (hf' n a).const_mul a)
      · intro i j hij x
        refine SimpleFunc.lintegral_mono ?_ (le_of_eq rfl)
        intro y
        dsimp only [f']
        exact SimpleFunc.monotone_eapprox f hij (x, y)
    _ = ∫⁻ (x : X), ∫⁻ (y : Y), f (x, y) ∂ν ∂μ := by
      refine lintegral_congr ?_
      intro x
      simp only [← hf'sup]
      have hlin_iSup : ∫⁻ y, ⨆ n, f' n x y ∂ν = ⨆ n, ∫⁻ y, f' n x y ∂ν :=
        lintegral_iSup (fun n ↦ SimpleFunc.measurable (f' n x))
          (fun i j hij y ↦ SimpleFunc.monotone_eapprox _ hij _)
      rw [hlin_iSup]
      apply iSup_congr (fun n ↦ ?_)
      rw [SimpleFunc.lintegral_eq_lintegral]

theorem prod_prod [SFinite ν]
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ.prod ν (A ×ˢ B) = μ A * ν B := by
  calc
    μ.prod ν (A ×ˢ B)
    _ = ∫⁻ x, ν (Prod.mk x ⁻¹' (A ×ˢ B)) ∂μ := prod_apply (by measurability)
    _ = μ A * ν B := by
      classical simp_rw [mk_preimage_prod_right_eq_if, measure_if]
      simp_rw [ lintegral_indicator hA, lintegral_const, restrict_apply_univ, mul_comm]

theorem prod_univ [SFinite ν] :
    μ.prod ν univ = μ univ * ν univ := by
  rw [← univ_prod_univ, prod_prod .univ .univ]

instance [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ.prod ν) := by
  refine ⟨?_⟩
  simpa [prod_univ] using
    mul_lt_top ((isFiniteMeasure_iff _).mp ‹_›) ((isFiniteMeasure_iff _).mp ‹_›)

theorem prod_swap_fin [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    map Prod.swap (ν.prod μ) = μ.prod ν := by
  ext A hA
  induction A, hA using induction_on_inter rfl (isPiSystem_genProd X Y) with
  | basic A hA =>
    obtain @⟨A, hA, B, hB⟩ := hA
    rw [prod_prod hA hB]
    rw [map_apply measurable_swap (hA.sProd hB)]
    rw [preimage_swap_prod]
    rw [prod_prod hB hA]
    rw [mul_comm]
  | empty => simp
  | compl A hA ih =>
    simp_rw [measure_compl hA (measure_lt_top _ _).ne, map_apply measurable_swap MeasurableSet.univ]
    rw [ih]
    simp_rw [preimage_univ, prod_univ, mul_comm]
  | iUnion A hdA hA ih =>
    rw [measure_iUnion hdA hA, measure_iUnion hdA hA]
    apply tsum_congr
    intro n
    exact ih n

theorem sum_prod_sum (μ : ℕ → Measure X) (ν : ℕ → Measure Y) [∀ i, SFinite (ν i)] :
    Measure.prod (sum μ) (sum ν) = sum (fun i ↦ sum (fun j ↦ (μ i).prod (ν j))) := by
  ext A hA
  simp_rw [Measure.sum_apply _ hA]
  simp_rw [prod_apply hA]
  rw [lintegral_sum_measure]
  apply tsum_congr
  intro i
  rw [← lintegral_tsum]
  · apply lintegral_congr
    intro x
    rw [sum_apply _ (measurable_prodMk_left hA)]
  · intro j
    exact (measurable_measure_prodMk_left hA).aemeasurable

theorem prod_swap_apply [SFinite μ] {A : Set (X × Y)} (hA : MeasurableSet A) :
    map Prod.swap (ν.prod μ) A = ∫⁻ y, μ ((fun x ↦ Prod.mk x y) ⁻¹' A) ∂ν := by
  rw [map_apply measurable_swap hA]
  rw [prod_apply (measurable_swap hA)]
  grind

theorem prod_swap [SFinite μ] [SFinite ν] :
    map Prod.swap (ν.prod μ) = μ.prod ν := by
  simp_rw [← sum_sfiniteSeq ν, ← sum_sfiniteSeq μ]
  simp_rw [sum_prod_sum]
  ext A hA
  simp_rw [sum_apply _ hA]
  simp_rw [map_apply measurable_swap hA]
  simp_rw [sum_apply _ (measurable_swap hA)]
  rw [@ENNReal.tsum_comm]
  apply tsum_congr (fun i ↦ tsum_congr (fun j ↦ ?_))
  rw [← prod_swap_fin]
  rw [map_apply measurable_swap (measurable_swap hA)]
  rw [preimage_preimage]
  simp

theorem lintegral_prod_swap_le [SFinite μ] [SFinite ν] (f : X × Y → ℝ≥0∞) :
    ∫⁻ z, f z.swap ∂ν.prod μ ≤ ∫⁻ z, f z ∂μ.prod ν := by
  simp_rw [lintegral]
  apply iSup₂_le (fun g hg ↦ ?_)
  let g' : SimpleFunc (X × Y) ℝ≥0∞ := g.comp Prod.swap measurable_swap
  apply le_iSup_of_le g'
  apply le_iSup_of_le (fun z ↦ hg z.swap : g' ≤ f)
  rw [← @SimpleFunc.lintegral_map]
  refine SimpleFunc.lintegral_mono_measure (le_of_eq prod_swap.symm)

theorem lintegral_prod_swap [SFinite μ] [SFinite ν] (f : X × Y → ℝ≥0∞) :
    ∫⁻ z, f z.swap ∂ν.prod μ = ∫⁻ z, f z ∂μ.prod ν := by
  apply le_antisymm <;> apply lintegral_prod_swap_le

theorem lintegral_prod_swap_of_measurable [SFinite μ] [SFinite ν]
    (f : X × Y → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z.swap ∂ν.prod μ = ∫⁻ z, f z ∂μ.prod ν := by
  have : ∀ z, f z.swap = (f ∘ Prod.swap) z := by grind
  calc
    _ = ∫⁻ z, (f (Prod.swap z)) ∂ν.prod μ := by
      apply lintegral_congr (by grind)
    _ = ∫⁻ z, f z ∂μ.prod ν := by
      rw [← lintegral_map hf measurable_swap]
      rw [@prod_swap]

theorem lintegral_prod_symm [SFinite μ] [SFinite ν] (f : X × Y → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  rw [← lintegral_prod_swap]
  rw [lintegral_prod (f := fun z : Y × X ↦ f z.swap) (hf.comp measurable_swap)]
  apply lintegral_congr (fun y ↦ lintegral_congr (fun x ↦ by grind [Prod.swap_prod_mk]))

/-- **Tonelli's Theorem** -/
theorem lintegral_prod_swap' [SFinite μ] [SFinite ν] (f : X × Y → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  rw [← lintegral_prod hf, ← lintegral_prod_symm f hf]

end Prod

end MTI
