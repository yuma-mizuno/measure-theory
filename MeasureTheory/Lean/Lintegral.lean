import MeasureTheory.Lean.SimpleFunc
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Map

set_option autoImplicit false

namespace MTI

open MeasureTheory Filter ENNReal Topology NNReal Set

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

section

noncomputable def lintegral (μ : Measure X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : SimpleFunc X) (_ : ⇑g ≤ f), g.lintegral μ

notation3 "∫⁻ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => lintegral μ r

theorem SimpleFunc.lintegral_eq_lintegral (f : SimpleFunc X) (μ : Measure X) :
    ∫⁻ a, f a ∂μ = f.lintegral μ := by
  exact le_antisymm (iSup₂_le fun g hg ↦ SimpleFunc.lintegral_mono hg <| le_rfl)
    (le_iSup₂_of_le f le_rfl le_rfl)

@[mono]
theorem lintegral_mono ⦃f g : X → ℝ≥0∞⦄ (hfg : f ≤ g) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ := by
  exact iSup_mono fun φ ↦ iSup_mono'
    fun hφ ↦ ⟨le_trans hφ hfg, SimpleFunc.lintegral_mono (le_refl φ) (le_of_eq rfl)⟩

@[gcongr]
theorem lintegral_mono_fn ⦃f g : X → ℝ≥0∞⦄ (hfg : ∀ x, f x ≤ g x) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono hfg

theorem monotone_lintegral (μ : Measure X) : Monotone (lintegral μ) :=
  lintegral_mono

theorem lintegral_zero : ∫⁻ _ : X, 0 ∂μ = 0 :=
  calc
    ∫⁻ _ : X, 0 ∂μ = (0 : SimpleFunc X).lintegral μ := SimpleFunc.lintegral_eq_lintegral 0 μ
    _ = 0 := SimpleFunc.zero_lintegral

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`g : X →ₛ ℝ≥0∞` such that `g ≤ f`. This lemma says that it suffices to take
simple functions `g : X → ℝ≥0`. -/
theorem lintegral_eq_nnreal (f : X → ℝ≥0∞) (μ : Measure X) :
    ∫⁻ a, f a ∂μ =
      ⨆ (g : SimpleFunc X) (_ : ∀ x, g x ≤ f x) (_ : ∀ x, g x ≠ ∞), g.lintegral μ := by
  rw [lintegral]
  refine
    le_antisymm (iSup₂_le fun g hg ↦ ?_) (iSup_mono' fun g ↦ ⟨g,
      iSup₂_le_iSup (fun i ↦ ∀ (x : X), g x ≠ ∞) fun i ↦ g.lintegral μ⟩)
  by_cases h : ∀ᵐ a ∂μ, g a ≠ ∞
  · let ψ := g.map (ENNReal.ofReal ∘ ENNReal.toReal)
    replace h : ψ =ᵐ[μ] g := h.mono fun a ha ↦ by simpa [ψ] using ha
    have : ∀ x, ↑(ψ x) ≤ f x := fun x ↦ le_trans ofReal_toReal_le (hg x)
    apply le_iSup₂_of_le ψ this
    refine le_iSup_of_le (fun x ↦ ?_) ?_
    · simp [ψ]
    · exact ge_of_eq <| SimpleFunc.lintegral_congr h
  · have h_meas : μ (g ⁻¹' {∞}) ≠ 0 := mt measure_eq_zero_iff_ae_notMem.1 h
    refine le_trans le_top (ge_of_eq <| (iSup_eq_top _).2 fun b hb ↦ ?_)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (g ⁻¹' {∞}) := exists_nat_mul_gt h_meas (ne_of_lt hb)
    let ψ := (SimpleFunc.const X (n : ℝ≥0)).restrict (g ⁻¹' {∞})
    have hs : MeasurableSet (g ⁻¹' {∞}) := SimpleFunc.measurableSet_preimage g {∞}
    have hψ : ∀ x, ↑(ψ x) ≤ f x := by
      intro x
      by_cases hx : x ∈ g ⁻¹' {∞}
      · have hfx : f x = ∞ := by
          simp only [mem_preimage, mem_singleton_iff] at hx
          exact top_le_iff.mp (hx ▸ hg x)
        simp [ψ, hs, hx, hfx]
      · simp [ψ, hs, hx]
    have hψ_int : ψ.lintegral μ = n * μ (g ⁻¹' {∞}) := SimpleFunc.restrict_const_lintegral n hs
    simp only [lt_iSup_iff, exists_prop]
    refine ⟨ψ, hψ, ?_, (by simpa [hψ_int] using hn)⟩
    intro x
    simp only [ψ, coe_natCast]
    rw [SimpleFunc.restrict_apply (SimpleFunc.const X ↑n) hs x]
    simp only [SimpleFunc.coe_const]
    suffices (g ⁻¹' {∞}).indicator (Function.const X ↑n) x < ∞ from this.ne
    apply lt_of_le_of_lt _ (?_ : Function.const X (n : ℝ≥0∞) x < ∞)
    · apply indicator_le (fun a ha ↦ le_refl _)
    · simp

theorem iSup_lintegral_le {ι : Sort*} (f : ι → X → ℝ≥0∞) :
    ⨆ i, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ⨆ i, f i a ∂μ := by
  simp only [← iSup_apply]
  exact (monotone_lintegral μ).le_map_iSup

theorem iSup₂_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → X → ℝ≥0∞) :
    ⨆ (i) (j), ∫⁻ a, f i j a ∂μ ≤ ∫⁻ a, ⨆ (i) (j), f i j a ∂μ := by
  convert (monotone_lintegral μ).le_map_iSup₂ f with a
  simp only [iSup_apply]

theorem le_iInf_lintegral {ι : Sort*} (f : ι → X → ℝ≥0∞) :
    ∫⁻ a, ⨅ i, f i a ∂μ ≤ ⨅ i, ∫⁻ a, f i a ∂μ := by
  simp only [← iInf_apply]
  exact (monotone_lintegral μ).map_iInf_le

theorem le_iInf₂_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → X → ℝ≥0∞) :
    ∫⁻ a, ⨅ (i) (h : ι' i), f i h a ∂μ ≤ ⨅ (i) (h : ι' i), ∫⁻ a, f i h a ∂μ := by
  convert (monotone_lintegral μ).map_iInf₂_le f with a
  simp only [iInf_apply]

theorem lintegral_congr {f g : X → ℝ≥0∞} (h : ∀ a, f a = g a) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  simp only [h]

theorem iSup_lintegral_measurable_le_eq_lintegral (f : X → ℝ≥0∞) :
    ⨆ (g : X → ℝ≥0∞) (_ : Measurable g) (_ : g ≤ f), ∫⁻ a, g a ∂μ = ∫⁻ a, f a ∂μ := by
  apply le_antisymm
  · exact iSup_le fun i ↦ iSup_le fun _ ↦ iSup_le fun h'i ↦ lintegral_mono h'i
  · rw [lintegral]
    refine iSup₂_le fun i hi ↦ le_iSup₂_of_le i i.measurable <| le_iSup_of_le hi ?_
    exact le_of_eq (i.lintegral_eq_lintegral _).symm

variable (μ) in
theorem exists_measurable_le_lintegral_eq (f : X → ℝ≥0∞) :
    ∃ g : X → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ := by
  rcases eq_or_ne (∫⁻ a, f a ∂μ) 0 with h₀ | h₀
  · exact ⟨0, measurable_zero, fun _ ↦ bot_le, h₀.trans lintegral_zero.symm⟩
  rcases exists_seq_strictMono_tendsto' h₀.bot_lt with ⟨L, _, hLf, hL_tendsto⟩
  have h_exists : ∀ n, ∃ g : X → ℝ≥0∞, Measurable g ∧ g ≤ f ∧ L n < ∫⁻ a, g a ∂μ := by
    intro n
    simpa only [← iSup_lintegral_measurable_le_eq_lintegral f, lt_iSup_iff, exists_prop] using
      (hLf n).2
  choose g hgm hgf hLg using h_exists
  refine ⟨fun x ↦ ⨆ n, g n x, .iSup hgm, fun x ↦ iSup_le fun n ↦ hgf n x, le_antisymm ?_ ?_⟩
  · refine le_of_tendsto' hL_tendsto fun n ↦ (hLg n).le.trans <| lintegral_mono fun x ↦ ?_
    exact le_iSup (fun n ↦ g n x) n
  · exact lintegral_mono fun x ↦ iSup_le fun n ↦ hgf n x

end

section MonotoneConvergence

theorem lintegral_iSup {f : ℕ → X → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ := by
  set c : ℝ≥0 → ℝ≥0∞ := (↑)
  set F := fun a : X ↦ ⨆ n, f n a
  refine le_antisymm ?_ (iSup_lintegral_le _)
  rw [lintegral_eq_nnreal]
  refine iSup_le fun s ↦ iSup_le fun hsf ↦ iSup_le fun hsfin ↦ ?_
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ ?_
  rcases ENNReal.lt_iff_exists_coe.1 ha with ⟨r, rfl, _⟩
  have ha : r < 1 := ENNReal.coe_lt_coe.1 ha
  let rs := s.map fun a ↦ r * a
  have eq_rs :
      rs =
        (SimpleFunc.const X r : SimpleFunc X) * s := rfl
  have eq : ∀ p, rs ⁻¹' {p} = ⋃ n, rs ⁻¹' {p} ∩ { a | p ≤ f n a } := by
    intro p
    rw [← inter_iUnion]; nth_rw 1 [← inter_univ (rs ⁻¹' {p})]
    refine Set.ext fun x ↦ and_congr_right fun hx ↦ (iff_of_eq (true_iff _)).2 ?_
    by_cases p_eq : p = 0
    · simp [p_eq]
    simp only [mem_preimage, mem_singleton_iff] at hx
    subst hx
    have : r * s x ≠ 0 := by rwa [Ne]
    have : s x ≠ 0 := right_ne_zero_of_mul this
    have : rs x < ⨆ n : ℕ, f n x := by
      refine lt_of_lt_of_le ?_ (hsf x)
      suffices r * s x < 1 * s x by simpa
      gcongr with a
      apply hsfin
    rcases lt_iSup_iff.1 this with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, le_of_lt hi⟩
  have mono :
      ∀ r : ℝ≥0∞, Monotone fun n ↦ rs ⁻¹' {r} ∩ { a | r ≤ f n a } := by
    intro r i j h
    refine inter_subset_inter_right _ ?_
    simp_rw [subset_def, mem_setOf]
    intro x hx
    exact le_trans hx (h_mono h x)
  have h_meas : ∀ n, MeasurableSet {a : X | rs a ≤ f n a} :=
    fun n ↦ measurableSet_le (SimpleFunc.measurable (rs)) (hf n)
  calc
    (r : ℝ≥0∞) * (s).lintegral μ =
        ((SimpleFunc.const X r : SimpleFunc X) * s).lintegral μ := by
      rw [SimpleFunc.const_mul_lintegral]
    _ = ∑ r ∈ (rs).range, r * μ (rs ⁻¹' {r}) := by
      rw [eq_rs]
      rfl
    _ = ∑ r ∈ (rs).range, r * μ (⋃ n, rs ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      simp only [(eq _).symm]
    _ = ∑ r ∈ (rs).range,
          ⨆ n, r * μ (rs ⁻¹' {r} ∩ { a | r ≤ f n a }) :=
      Finset.sum_congr rfl fun x _ ↦ by rw [(mono x).measure_iUnion, ENNReal.mul_iSup]
    _ = ⨆ n, ∑ r ∈ (rs).range,
          r * μ (rs ⁻¹' {r} ∩ { a | r ≤ f n a }) := by
      refine ENNReal.finsetSum_iSup_of_monotone fun p i j h ↦ ?_
      gcongr _ * μ ?_
      exact mono p h
    _ ≤ ⨆ n : ℕ,
          ((rs).restrict { a | rs a ≤ f n a }).lintegral μ := by
      gcongr with n
      rw [SimpleFunc.restrict_lintegral _ (h_meas n)]
      refine le_of_eq (Finset.sum_congr rfl fun r _ ↦ ?_)
      congr 2 with a
      refine and_congr_right ?_
      simp +contextual
    _ ≤ ⨆ n, ∫⁻ a, f n a ∂μ := by
      refine iSup_le fun n ↦ ?_
      refine le_iSup_of_le n ?_
      let t := (rs).restrict { a | rs a ≤ f n a }
      have ht : ∀ a, t a ≤ f n a := by
        intro a
        dsimp [t]
        simp only [SimpleFunc.restrict_apply _ (h_meas _)]
        exact indicator_apply_le id
      exact (SimpleFunc.lintegral_eq_lintegral t μ).ge.trans (lintegral_mono ht)

end MonotoneConvergence

section Add

theorem lintegral_eq_iSup_eapprox_lintegral {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ⨆ n, (SimpleFunc.eapprox f n).lintegral μ :=
  calc
    ∫⁻ a, f a ∂μ = ∫⁻ a, ⨆ n, (SimpleFunc.eapprox f n : X → ℝ≥0∞) a ∂μ :=
      lintegral_congr (fun x ↦ (SimpleFunc.iSup_eapprox_apply hf x).symm)
    _ = ⨆ n, ∫⁻ a, (SimpleFunc.eapprox f n : X → ℝ≥0∞) a ∂μ :=
      lintegral_iSup (fun n ↦ (SimpleFunc.eapprox f n).measurable) (SimpleFunc.monotone_eapprox f)
    _ = ⨆ n, (SimpleFunc.eapprox f n).lintegral μ :=
      iSup_congr (fun n ↦ (SimpleFunc.eapprox f n).lintegral_eq_lintegral μ)

theorem lintegral_map {Y : Type*} [MeasurableSpace Y] {ν : Measure X} {f : X → Y}
    {g : Y → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) :
    ∫⁻ y, g y ∂(Measure.map f ν) = ∫⁻ x, g (f x) ∂ν := by
  let h n : SimpleFunc X := {
    toFun := (SimpleFunc.eapprox g n) ∘ f
    measurableSet_fiber' := fun a ↦ by
      apply (SimpleFunc.measurable (SimpleFunc.eapprox g n)).comp hf
      exact measurableSet_singleton a
    finite_range' := by
      rw [@range_comp]
      have hsubset :
          (⇑(SimpleFunc.eapprox g n) '' range f) ⊆ range (SimpleFunc.eapprox g n) := by
        exact image_subset_range (⇑(SimpleFunc.eapprox g n)) (range f)
      exact Set.Finite.subset (SimpleFunc.finite_range (SimpleFunc.eapprox g n)) hsubset }
  calc
    ∫⁻ y, g y ∂(Measure.map f ν) =
        ⨆ n, ∫⁻ y, (SimpleFunc.eapprox g n) y ∂(Measure.map f ν) := by
      rw [lintegral_eq_iSup_eapprox_lintegral hg]
      apply iSup_congr
      intro n
      rw [SimpleFunc.lintegral_eq_lintegral]
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * Measure.map f ν ((SimpleFunc.eapprox g n) ⁻¹' {a}) := by
      apply iSup_congr
      intro n
      rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * ν (f ⁻¹' ((SimpleFunc.eapprox g n) ⁻¹' {a})) := by
      apply iSup_congr
      intro n
      congr 1 with a
      congr 1
      rw [Measure.map_apply hf]
      exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox g n) a
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * ν ((SimpleFunc.eapprox g n ∘ f) ⁻¹' {a}) := by
      rfl
    _ = ⨆ n, ∑ a ∈ (h n).range, a * ν (h n ⁻¹' {a}) := by
      apply iSup_congr
      intro n
      apply Eq.symm
      apply Finset.sum_subset
      · intro a
        simp only [SimpleFunc.mem_range, mem_range, forall_exists_index]
        intro x hx
        exact ⟨f x, by simpa [h] using hx⟩
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
    _ = ⨆ n, ∫⁻ x, (h n) x ∂ν := by
      apply iSup_congr
      intro n
      rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
    _ = ∫⁻ x, (g ∘ f) x ∂ν := by
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

theorem lintegral_const_mul {f : X → ℝ≥0∞} (c : ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ a, c * f a ∂μ = c * ∫⁻ a, f a ∂μ := by
  calc
    ∫⁻ a, c * f a ∂μ =
        ∫⁻ a, c * ⨆ n, (SimpleFunc.eapprox f n : X → ℝ≥0∞) a ∂μ := by
      apply lintegral_congr
      intro x
      rw [SimpleFunc.iSup_eapprox_apply hf x]
    _ = ∫⁻ a, ⨆ n, (SimpleFunc.const X c * SimpleFunc.eapprox f n : SimpleFunc X) a ∂μ := by
      apply lintegral_congr
      intro x
      rw [ENNReal.mul_iSup]
      simp
    _ = ⨆ n, ∫⁻ a, (SimpleFunc.const X c * SimpleFunc.eapprox f n : SimpleFunc X) a ∂μ := by
      exact lintegral_iSup
        (fun n ↦ (SimpleFunc.const X c * SimpleFunc.eapprox f n).measurable)
        (by
          intro i j hij x
          change c * (SimpleFunc.eapprox f i x) ≤ c * (SimpleFunc.eapprox f j x)
          gcongr
          exact SimpleFunc.monotone_eapprox f hij x)
    _ = ⨆ n, (SimpleFunc.const X c * SimpleFunc.eapprox f n).lintegral μ := by
      refine iSup_congr fun n ↦ ?_
      exact SimpleFunc.lintegral_eq_lintegral (SimpleFunc.const X c * SimpleFunc.eapprox f n) μ
    _ = ⨆ n, c * (SimpleFunc.eapprox f n).lintegral μ := by
      refine iSup_congr fun n ↦ ?_
      rw [SimpleFunc.const_mul_lintegral]
    _ = c * ⨆ n, (SimpleFunc.eapprox f n).lintegral μ := by
      rw [ENNReal.mul_iSup]
    _ = c * ∫⁻ a, f a ∂μ := by
      rw [lintegral_eq_iSup_eapprox_lintegral hf]

theorem lintegral_add {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  calc
    ∫⁻ a, f a + g a ∂μ =
        ∫⁻ a,
          (⨆ n, (SimpleFunc.eapprox f n : X → ℝ≥0∞) a) +
            ⨆ n, (SimpleFunc.eapprox g n : X → ℝ≥0∞) a ∂μ := by
      simp only [SimpleFunc.iSup_eapprox_apply, hf, hg]
    _ = ∫⁻ a, ⨆ n, (SimpleFunc.eapprox f n + SimpleFunc.eapprox g n : X → ℝ≥0∞) a ∂μ := by
      congr; funext a
      rw [ENNReal.iSup_add_iSup_of_monotone]
      · simp only [Pi.add_apply]
      · intro i j h
        exact SimpleFunc.monotone_eapprox _ h a
      · intro i j h
        exact SimpleFunc.monotone_eapprox _ h a
    _ = ⨆ n, (SimpleFunc.eapprox f n).lintegral μ + (SimpleFunc.eapprox g n).lintegral μ := by
      rw [lintegral_iSup]
      · apply iSup_congr (fun n ↦ ?_)
        calc
          ∫⁻ a, (SimpleFunc.eapprox f n + SimpleFunc.eapprox g n : X → ℝ≥0∞) a ∂μ =
              (SimpleFunc.eapprox f n + SimpleFunc.eapprox g n).lintegral μ :=
            by
              simpa [SimpleFunc.coe_add, Pi.add_apply] using
                (SimpleFunc.lintegral_eq_lintegral
                  (SimpleFunc.eapprox f n + SimpleFunc.eapprox g n) μ)
          _ = (SimpleFunc.eapprox f n).lintegral μ + (SimpleFunc.eapprox g n).lintegral μ := by
            exact SimpleFunc.add_lintegral _ _
      · intro n
        exact (SimpleFunc.eapprox f n + SimpleFunc.eapprox g n).measurable
      · intro i j h a
        exact add_le_add (SimpleFunc.monotone_eapprox f h _) (SimpleFunc.monotone_eapprox g h _)
    _ = (⨆ n, (SimpleFunc.eapprox f n).lintegral μ) +
          ⨆ n, (SimpleFunc.eapprox g n).lintegral μ := by
      refine (ENNReal.iSup_add_iSup_of_monotone ?_ ?_).symm <;>
        · intro i j h
          exact SimpleFunc.lintegral_mono (SimpleFunc.monotone_eapprox _ h) le_rfl
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
      rw [lintegral_eq_iSup_eapprox_lintegral hf, lintegral_eq_iSup_eapprox_lintegral hg]

theorem le_lintegral_add (f g : X → ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ ≤ ∫⁻ a, f a + g a ∂μ := by
  simp only [lintegral]
  refine ENNReal.biSup_add_biSup_le' (p := fun h : SimpleFunc X => h ≤ f)
    (q := fun h : SimpleFunc X => h ≤ g) ⟨0, fun _ ↦ bot_le⟩ ⟨0, fun _ ↦ bot_le⟩
    fun f' hf' g' hg' => ?_
  exact le_iSup₂_of_le (f' + g') (fun x ↦ add_le_add (hf' x) (hg' x))
    (SimpleFunc.add_lintegral _ _).ge

theorem lintegral_add_left {f : X → ℝ≥0∞} (hf : Measurable f) (g : X → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  refine le_antisymm ?_ (le_lintegral_add _ _)
  rcases exists_measurable_le_lintegral_eq μ (fun a ↦ f a + g a) with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, φ a ∂μ := hφ_eq
    _ ≤ ∫⁻ a, f a + (φ a - f a) ∂μ := lintegral_mono fun a ↦ le_add_tsub
    _ = ∫⁻ a, f a ∂μ + ∫⁻ a, φ a - f a ∂μ := lintegral_add hf (hφm.sub hf)
    _ ≤ ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
      gcongr with a
      exact tsub_le_iff_left.2 <| hφ_le a

theorem lintegral_add_right (f : X → ℝ≥0∞) {g : X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ := by
  simpa only [add_comm] using lintegral_add_left hg f

end Add

section Sub

theorem lintegral_sub {f g : X → ℝ≥0∞}
    (hg : Measurable g) (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞) (h_le : g ≤ f) :
    ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ := by
  refine ENNReal.eq_sub_of_add_eq hg_fin ?_
  rw [← lintegral_add_right (fun a ↦ f a - g a) hg]
  exact lintegral_congr (fun x ↦ tsub_add_cancel_of_le (h_le x))

theorem lintegral_iInf {f : ℕ → X → ℝ≥0∞}
    (h_meas : ∀ n, Measurable (f n)) (h_anti : Antitone f)
    (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) : ∫⁻ a, ⨅ n, f n a ∂μ = ⨅ n, ∫⁻ a, f n a ∂μ :=
  have fn_le_f0 : ∫⁻ a, ⨅ n, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ :=
    lintegral_mono fun _ ↦ iInf_le_of_le 0 le_rfl
  have fn_le_f0' : ⨅ n, ∫⁻ a, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ := iInf_le_of_le 0 le_rfl
  (ENNReal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1 <|
    show ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 a ∂μ - ⨅ n, ∫⁻ a, f n a ∂μ from
      calc
        ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅ n, f n a ∂μ = ∫⁻ a, f 0 a - ⨅ n, f n a ∂μ :=
          (lintegral_sub (Measurable.iInf h_meas)
            (ne_top_of_le_ne_top h_fin fn_le_f0) (fun a ↦ iInf_le _ _)).symm
        _ = ∫⁻ a, ⨆ n, f 0 a - f n a ∂μ := congr rfl (funext fun _ ↦ ENNReal.sub_iInf)
        _ = ⨆ n, ∫⁻ a, f 0 a - f n a ∂μ := by
          apply lintegral_iSup (fun n ↦ (h_meas 0).sub (h_meas n))
          intro i j h a
          exact tsub_le_tsub_left (h_anti h a) (f 0 a)
        _ = ⨆ n, ∫⁻ a, f 0 a ∂μ - ∫⁻ a, f n a ∂μ :=
          (have h_mono : ∀ a, ∀ n : ℕ, f n.succ a ≤ f n a := fun a n ↦ h_anti (Nat.le_succ n) a
          have h_mono : ∀ n, ∀ a, f n a ≤ f 0 a := fun n a ↦ h_anti (Nat.zero_le n) _
          congr_arg iSup <|
            funext fun n ↦
              lintegral_sub (h_meas n)
                (ne_top_of_le_ne_top h_fin (lintegral_mono (h_mono n))) (h_mono n))
        _ = ∫⁻ a, f 0 a ∂μ - ⨅ n, ∫⁻ a, f n a ∂μ := ENNReal.sub_iInf.symm

end Sub

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem limsup_lintegral_le {f : ℕ → X → ℝ≥0∞}
    (g : X → ℝ≥0∞) (hf_meas : ∀ n, Measurable (f n))
    (h_bound : ∀ n, f n ≤ g) (h_fin : ∫⁻ a, g a ∂μ ≠ ∞) :
    limsup (fun n ↦ ∫⁻ a, f n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n ↦ f n a) atTop ∂μ :=
  calc
    limsup (fun n ↦ ∫⁻ a, f n a ∂μ) atTop = ⨅ n : ℕ, ⨆ i ≥ n, ∫⁻ a, f i a ∂μ :=
      limsup_eq_iInf_iSup_of_nat
    _ ≤ ⨅ n : ℕ, ∫⁻ a, ⨆ i ≥ n, f i a ∂μ := iInf_mono fun _ ↦ iSup₂_lintegral_le _
    _ = ∫⁻ a, ⨅ n : ℕ, ⨆ i ≥ n, f i a ∂μ := by
      refine (lintegral_iInf ?_ ?_ ?_).symm
      · intro n
        exact .biSup _ (Set.to_countable _) (fun i _ ↦ hf_meas i)
      · intro n m hnm a
        exact iSup_le_iSup_of_subset fun i hi ↦ le_trans hnm hi
      · refine ne_top_of_le_ne_top h_fin (lintegral_mono ?_)
        refine fun n ↦ ?_
        exact iSup_le fun i ↦ iSup_le fun _ ↦ (h_bound i n)
    _ = ∫⁻ a, limsup (fun n ↦ f n a) atTop ∂μ := by simp only [limsup_eq_iInf_iSup_of_nat]

theorem lintegral_liminf_le {f : ℕ → X → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) :
    ∫⁻ a, liminf (fun n ↦ f n a) atTop ∂μ ≤ liminf (fun n ↦ ∫⁻ a, f n a ∂μ) atTop :=
  calc
    ∫⁻ a, liminf (fun n ↦ f n a) atTop ∂μ = ∫⁻ a, ⨆ n : ℕ, ⨅ i ≥ n, f i a ∂μ := by
      simp only [liminf_eq_iSup_iInf_of_nat]
    _ = ⨆ n : ℕ, ∫⁻ a, ⨅ i ≥ n, f i a ∂μ :=
      (lintegral_iSup (fun _ ↦ .biInf _ (to_countable _) (fun i _ ↦ h_meas i))
        (fun _ _ hnm _ ↦ iInf_le_iInf_of_subset fun _ hi ↦ le_trans hnm hi))
    _ ≤ ⨆ n : ℕ, ⨅ i ≥ n, ∫⁻ a, f i a ∂μ := iSup_mono fun _ ↦ le_iInf₂_lintegral _
    _ = atTop.liminf fun n ↦ ∫⁻ a, f n a ∂μ := Filter.liminf_eq_iSup_iInf_of_nat.symm

theorem tendsto_lintegral_of_dominated_convergence
    {F : ℕ → X → ℝ≥0∞} {f : X → ℝ≥0∞}
    (bound : X → ℝ≥0∞) (hF_meas : ∀ n, Measurable (F n)) (h_bound : ∀ n, F n ≤ bound)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ a, Tendsto (fun n ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) :=
  tendsto_of_le_liminf_of_limsup_le
    (calc
      ∫⁻ a, f a ∂μ = ∫⁻ a, liminf (fun n : ℕ ↦ F n a) atTop ∂μ :=
        lintegral_congr <| fun a ↦ (h_lim a).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le hF_meas)
    (calc
      limsup (fun n : ℕ ↦ ∫⁻ a, F n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n ↦ F n a) atTop ∂μ :=
        limsup_lintegral_le _ hF_meas h_bound h_fin
      _ = ∫⁻ a, f a ∂μ := lintegral_congr <| fun a ↦ (h_lim a).limsup_eq)

end MTI
