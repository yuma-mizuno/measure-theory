import MeasureTheory.Lean.Lebesgue.SimpleFunc
import MeasureTheory.Lean.Lebesgue.Measurable

set_option autoImplicit false

noncomputable section

open Function Filter ENNReal Topology NNReal Set

namespace MTI

namespace Real

open SimpleFunc

/-- Lower Lebesgue integral on `ℝ`. -/
noncomputable def lintegral (f : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (g : SimpleFunc) (_ : ⇑g ≤ f), g.lintegral

notation3 (priority := high) "∫⁻ "(...)", " r:60:(scoped f => f) => lintegral r

theorem lintegral_eq_lintegral (f : SimpleFunc) :
    ∫⁻ x, f x = f.lintegral := by
  exact le_antisymm
    (iSup₂_le fun g hg ↦ lintegral_mono_fun (f := g) (g := f) hg)
    (le_iSup₂_of_le f le_rfl le_rfl)

@[mono]
theorem lintegral_mono ⦃f g : ℝ → ℝ≥0∞⦄ (hfg : f ≤ g) :
    ∫⁻ x, f x ≤ ∫⁻ x, g x := by
  exact iSup_mono fun φ ↦ iSup_mono' fun hφ ↦
    ⟨le_trans hφ hfg, lintegral_mono_fun le_rfl⟩

theorem lintegral_congr {f g : ℝ → ℝ≥0∞} (h : ∀ x, f x = g x) :
    ∫⁻ x, f x = ∫⁻ x, g x := by
  apply le_antisymm
  · exact lintegral_mono fun x ↦ le_of_eq (h x)
  · exact lintegral_mono fun x ↦ le_of_eq (h x).symm

theorem lintegral_zero : ∫⁻ _x, (0 : ℝ≥0∞) = 0 := by
  calc
    ∫⁻ x, (0 : ℝ≥0∞) = ∫⁻ x, (0 : SimpleFunc) x := by
      apply lintegral_congr
      intro x
      simp
    _ = (0 : SimpleFunc).lintegral := by
      simpa using (lintegral_eq_lintegral (0 : SimpleFunc))
    _ = 0 := zero_lintegral

/-- It suffices to take the supremum over finite-valued simple functions. -/
theorem lintegral_eq_nnreal (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x =
      ⨆ (g : SimpleFunc) (_ : ∀ x, g x ≤ f x) (_ : ∀ x, g x ≠ ∞), g.lintegral := by
  rw [lintegral]
  refine
    le_antisymm (iSup₂_le fun g hg ↦ ?_) (iSup_mono' fun g ↦ ⟨g,
      iSup₂_le_iSup (fun i ↦ ∀ x : ℝ, g x ≠ ∞) fun i ↦ g.lintegral⟩)
  by_cases h : measure (g ⁻¹' {∞}) = 0
  · let ψ := g.map (ENNReal.ofReal ∘ ENNReal.toReal)
    have hψ : ∀ x, ψ x ≤ f x := fun x ↦ le_trans ENNReal.ofReal_toReal_le (hg x)
    apply le_iSup₂_of_le ψ hψ
    refine le_iSup_of_le (fun x ↦ ?_) ?_
    · simp [ψ]
    · apply ge_of_eq
      calc
        ψ.lintegral =
            ψ.lintegralIn univ := by
              exact ψ.lintegral_eq_lintegralIn_univ
        _ = ∑ y ∈ g.range, ENNReal.ofReal (ENNReal.toReal y) * measure (g ⁻¹' {y}) := by
              simpa [ψ] using
                (map_lintegralIn (ENNReal.ofReal ∘ ENNReal.toReal) g
                  (s := univ) MeasurableSet.univ)
        _ = ∑ y ∈ g.range, y * measure (g ⁻¹' {y}) := by
              refine Finset.sum_congr rfl fun y _ ↦ ?_
              by_cases hy : y = ∞
              · subst hy
                simp [h]
              · rw [ENNReal.ofReal_toReal hy]
        _ = g.lintegral := by
              simpa [lintegralIn] using g.lintegral_eq_lintegralIn_univ.symm
  · refine le_trans le_top (ge_of_eq <| (iSup_eq_top _).2 fun b hb ↦ ?_)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * measure (g ⁻¹' {∞}) :=
      exists_nat_mul_gt h (ne_of_lt hb)
    let ψ := (const n).restrict (g ⁻¹' {∞})
    have hs : MeasurableSet (g ⁻¹' {∞}) := g.measurableSet_fiber ∞
    have hψ : ∀ x, ψ x ≤ f x := by
      intro x
      by_cases hx : x ∈ g ⁻¹' {∞}
      · have hfx : f x = ∞ := by
          simp only [mem_preimage, mem_singleton_iff] at hx
          exact top_le_iff.mp (hx ▸ hg x)
        simp [ψ, hs, hx, hfx]
      · simp [ψ, hs, hx]
    have hψ_int : ψ.lintegral = n * measure (g ⁻¹' {∞}) := by
      simpa [ψ] using (restrict_const_lintegral n hs)
    simp only [lt_iSup_iff, exists_prop]
    refine ⟨ψ, hψ, ?_, by simpa [hψ_int] using hn⟩
    intro x
    by_cases hx : x ∈ g ⁻¹' {∞}
    · simp [ψ, hs, hx]
    · simp [ψ, hs, hx]

theorem iSup_lintegral_le {ι : Sort*} (f : ι → ℝ → ℝ≥0∞) :
    ⨆ i, ∫⁻ x, f i x ≤ ∫⁻ x, ⨆ i, f i x := by
  refine iSup_le fun i ↦ ?_
  exact lintegral_mono fun x ↦ le_iSup (fun j ↦ f j x) i

theorem iSup₂_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → ℝ → ℝ≥0∞) :
    ⨆ (i) (j), ∫⁻ x, f i j x ≤ ∫⁻ x, ⨆ (i) (j), f i j x := by
  refine iSup_le fun i ↦ iSup_le fun j ↦ ?_
  exact lintegral_mono fun x ↦ le_iSup_of_le i <| le_iSup (fun j ↦ f i j x) j

theorem le_iInf_lintegral {ι : Sort*} (f : ι → ℝ → ℝ≥0∞) :
    ∫⁻ x, ⨅ i, f i x ≤ ⨅ i, ∫⁻ x, f i x := by
  refine le_iInf fun i ↦ ?_
  exact lintegral_mono fun x ↦ iInf_le (fun j ↦ f j x) i

theorem le_iInf₂_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : ∀ i, ι' i → ℝ → ℝ≥0∞) :
    ∫⁻ x, ⨅ (i) (j), f i j x ≤ ⨅ (i) (j), ∫⁻ x, f i j x := by
  refine le_iInf fun i ↦ le_iInf fun j ↦ ?_
  exact lintegral_mono fun x ↦ iInf_le_of_le i <| iInf_le (fun j ↦ f i j x) j

theorem lintegral_iSup {f : ℕ → ℝ → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (h_mono : Monotone f) :
    ∫⁻ x, ⨆ n, f n x = ⨆ n, ∫⁻ x, f n x := by
  set F := fun x : ℝ ↦ ⨆ n, f n x
  refine le_antisymm ?_ (iSup_lintegral_le _)
  rw [lintegral_eq_nnreal]
  refine iSup_le fun s ↦ iSup_le fun hsf ↦ iSup_le fun hsfin ↦ ?_
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ ?_
  rcases ENNReal.lt_iff_exists_coe.1 ha with ⟨r, rfl, _⟩
  let rs := s.map fun y ↦ r * y
  have eq_rs : rs = (const r) * s := rfl
  have eq :
      ∀ p, rs ⁻¹' {p} = ⋃ n, rs ⁻¹' {p} ∩ {x | p ≤ f n x} := by
    intro p
    rw [← inter_iUnion]
    nth_rw 1 [← inter_univ (rs ⁻¹' {p})]
    refine Set.ext fun x ↦ and_congr_right fun hx ↦ (iff_of_eq (true_iff _)).2 ?_
    by_cases hp : p = 0
    · simp [hp]
    simp only [mem_preimage, mem_singleton_iff] at hx
    subst hx
    have hne : r * s x ≠ 0 := by rwa [Ne]
    have hsx_ne : s x ≠ 0 := right_ne_zero_of_mul hne
    have hsx_lt : rs x < ⨆ n : ℕ, f n x := by
      refine lt_of_lt_of_le ?_ (hsf x)
      suffices r * s x < 1 * s x by simpa [rs, eq_rs]
      gcongr with y
      exact hsfin x
    rcases lt_iSup_iff.1 hsx_lt with ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, le_of_lt hn⟩
  have mono :
      ∀ p : ℝ≥0∞, Monotone fun n ↦ rs ⁻¹' {p} ∩ {x | p ≤ f n x} := by
    intro p i j hij
    refine inter_subset_inter_right _ ?_
    intro x hx
    exact le_trans hx (h_mono hij x)
  have h_meas : ∀ n, MeasurableSet {x : ℝ | rs x ≤ f n x} :=
    fun n ↦ measurableSet_le rs (hf n)
  calc
    (r : ℝ≥0∞) * s.lintegral = ((const r) * s).lintegral := by
      rw [const_mul_lintegral]
    _ = ∑ p ∈ rs.range, p * measure (rs ⁻¹' {p}) := by
      rw [eq_rs]
      simp [SimpleFunc.lintegral]
    _ = ∑ p ∈ rs.range, p * measure (⋃ n, rs ⁻¹' {p} ∩ {x | p ≤ f n x}) := by
      refine Finset.sum_congr rfl fun p _ ↦ by rw [(eq p).symm]
    _ = ∑ p ∈ rs.range, ⨆ n, p * measure (rs ⁻¹' {p} ∩ {x | p ≤ f n x}) := by
      refine Finset.sum_congr rfl fun p _ ↦ by
        rw [measure_iUnion_of_monotone (mono p), ENNReal.mul_iSup]
    _ = ⨆ n, ∑ p ∈ rs.range, p * measure (rs ⁻¹' {p} ∩ {x | p ≤ f n x}) := by
      refine ENNReal.finsetSum_iSup_of_monotone fun p i j hij ↦ ?_
      exact mul_le_mul_right (measure_mono (mono p hij)) p
    _ ≤ ⨆ n, (rs.restrict {x | rs x ≤ f n x}).lintegral := by
      gcongr with n
      rw [restrict_lintegral _ (h_meas n)]
      refine le_of_eq <| Finset.sum_congr rfl fun p _ ↦ ?_
      congr 2 with x
      refine and_congr_right fun hx ↦ ?_
      simp only [mem_preimage, mem_singleton_iff] at hx
      simp [hx]
    _ ≤ ⨆ n, ∫⁻ x, f n x := by
      refine iSup_le fun n ↦ ?_
      refine le_iSup_of_le n ?_
      let t := rs.restrict {x | rs x ≤ f n x}
      have ht : ∀ x, t x ≤ f n x := by
        intro x
        dsimp only [t]
        rw [restrict_apply _ (h_meas n)]
        by_cases hx : rs x ≤ f n x
        · simp [hx]
        · simp [hx]
      exact (lintegral_eq_lintegral t).ge.trans (lintegral_mono ht)

theorem lintegral_eq_iSup_eapprox_lintegral {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ⨆ n, (eapprox f n).lintegral := by
  calc
    ∫⁻ x, f x = ∫⁻ x, ⨆ n, (eapprox f n : ℝ → ℝ≥0∞) x := by
      apply lintegral_congr
      intro x
      exact (iSup_eapprox_apply hf x).symm
    _ = ⨆ n, ∫⁻ x, (eapprox f n : ℝ → ℝ≥0∞) x := by
      exact lintegral_iSup (fun n ↦ (eapprox f n).measurable)
        (monotone_eapprox f)
    _ = ⨆ n, (eapprox f n).lintegral := by
      refine iSup_congr fun n ↦ ?_
      exact lintegral_eq_lintegral (eapprox f n)

theorem lintegral_const_mul {f : ℝ → ℝ≥0∞} (c : ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, c * f x = c * ∫⁻ x, f x := by
  calc
    ∫⁻ x, c * f x =
        ∫⁻ x, c * ⨆ n, (eapprox f n : ℝ → ℝ≥0∞) x := by
      apply lintegral_congr
      intro x
      rw [iSup_eapprox_apply hf x]
    _ = ∫⁻ x, ⨆ n, (const c * eapprox f n : SimpleFunc) x := by
      apply lintegral_congr
      intro x
      rw [ENNReal.mul_iSup]
      simp
    _ = ⨆ n, ∫⁻ x, (const c * eapprox f n : SimpleFunc) x := by
      exact lintegral_iSup
        (fun n ↦ (const c * eapprox f n).measurable)
        (by
          intro i j hij x
          exact mul_le_mul_right (monotone_eapprox f hij x) c)
    _ = ⨆ n, (const c * eapprox f n).lintegral := by
      refine iSup_congr fun n ↦ ?_
      exact lintegral_eq_lintegral (const c * eapprox f n)
    _ = ⨆ n, c * (eapprox f n).lintegral := by
      refine iSup_congr fun n ↦ ?_
      rw [const_mul_lintegral]
    _ = c * ⨆ n, (eapprox f n).lintegral := by
      rw [ENNReal.mul_iSup]
    _ = c * ∫⁻ x, f x := by
      rw [lintegral_eq_iSup_eapprox_lintegral hf]

theorem lintegral_add {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, f x + g x = (∫⁻ x, f x) + (∫⁻ x, g x) := by
  calc
    ∫⁻ x, f x + g x =
        (∫⁻ x,
          (⨆ n, (eapprox f n : ℝ → ℝ≥0∞) x) +
            ⨆ n, (eapprox g n : ℝ → ℝ≥0∞) x) := by
      apply lintegral_congr
      intro x
      simp only [iSup_eapprox_apply, hf, hg]
    _ = (∫⁻ x, ⨆ n, (eapprox f n + eapprox g n : SimpleFunc) x) := by
      apply lintegral_congr
      intro x
      rw [ENNReal.iSup_add_iSup_of_monotone]
      · rfl
      · intro i j hij
        exact monotone_eapprox _ hij x
      · intro i j hij
        exact monotone_eapprox _ hij x
    _ = ⨆ n, (eapprox f n).lintegral + (eapprox g n).lintegral := by
      rw [lintegral_iSup]
      · refine iSup_congr fun n ↦ ?_
        calc
          (∫⁻ x, (eapprox f n + eapprox g n : SimpleFunc) x) =
              (eapprox f n + eapprox g n).lintegral := by
                simpa [SimpleFunc.coe_add, Pi.add_apply] using
                  (lintegral_eq_lintegral
                    (eapprox f n + eapprox g n))
          _ = (eapprox f n).lintegral + (eapprox g n).lintegral := by
                exact add_lintegral _ _
      · intro n
        exact (eapprox f n + eapprox g n).measurable
      · intro i j hij x
        exact add_le_add (monotone_eapprox f hij x) (monotone_eapprox g hij x)
    _ = (⨆ n, (eapprox f n).lintegral) +
          ⨆ n, (eapprox g n).lintegral := by
      refine (ENNReal.iSup_add_iSup_of_monotone ?_ ?_).symm
      · intro i j hij
        exact lintegral_mono_fun (monotone_eapprox f hij)
      · intro i j hij
        exact lintegral_mono_fun (monotone_eapprox g hij)
    _ = (∫⁻ x, f x) + (∫⁻ x, g x) := by
      rw [lintegral_eq_iSup_eapprox_lintegral hf, lintegral_eq_iSup_eapprox_lintegral hg]

theorem le_lintegral_add (f g : ℝ → ℝ≥0∞) :
    (∫⁻ x, f x) + (∫⁻ x, g x) ≤ ∫⁻ x, f x + g x := by
  simp only [lintegral]
  refine ENNReal.biSup_add_biSup_le'
    (p := fun h : SimpleFunc => h ≤ f) (q := fun h : SimpleFunc => h ≤ g)
    ⟨0, fun _ ↦ bot_le⟩ ⟨0, fun _ ↦ bot_le⟩ fun f' hf' g' hg' ↦ ?_
  exact le_iSup₂_of_le (f' + g') (fun x ↦ add_le_add (hf' x) (hg' x))
    (add_lintegral _ _).ge

theorem lintegral_sub {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hg_fin : ∫⁻ x, g x ≠ ∞) (h_le : g ≤ f) :
    ∫⁻ x, f x - g x = (∫⁻ x, f x) - (∫⁻ x, g x) := by
  refine ENNReal.eq_sub_of_add_eq hg_fin ?_
  rw [← lintegral_add (hf.sub hg) hg]
  exact lintegral_congr fun x ↦ tsub_add_cancel_of_le (h_le x)

theorem lintegral_iInf {f : ℕ → ℝ → ℝ≥0∞}
    (h_meas : ∀ n, Measurable (f n)) (h_anti : Antitone f) (h_fin : ∫⁻ x, f 0 x ≠ ∞) :
    ∫⁻ x, ⨅ n, f n x = ⨅ n, ∫⁻ x, f n x :=
  have fn_le_f0 : ∫⁻ x, ⨅ n, f n x ≤ ∫⁻ x, f 0 x :=
    lintegral_mono fun _ ↦ iInf_le_of_le 0 le_rfl
  have fn_le_f0' : (⨅ n, ∫⁻ x, f n x) ≤ ∫⁻ x, f 0 x := iInf_le_of_le 0 le_rfl
  (ENNReal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1 <|
    show (∫⁻ x, f 0 x) - (∫⁻ x, ⨅ n, f n x) =
        (∫⁻ x, f 0 x) - (⨅ n, ∫⁻ x, f n x) from
      calc
        (∫⁻ x, f 0 x) - (∫⁻ x, ⨅ n, f n x) =
            (∫⁻ x, f 0 x - ⨅ n, f n x) := by
              symm
              exact lintegral_sub (h_meas 0) (.iInf h_meas)
                (ne_top_of_le_ne_top h_fin fn_le_f0) fun x ↦ iInf_le _ _
        _ = ∫⁻ x, ⨆ n, f 0 x - f n x := by
              congr
              funext x
              rw [ENNReal.sub_iInf]
        _ = ⨆ n, (∫⁻ x, f 0 x - f n x) := by
              apply lintegral_iSup
              · intro n
                exact (h_meas 0).sub (h_meas n)
              · intro i j h x
                exact tsub_le_tsub_left (h_anti h x) (f 0 x)
        _ = ⨆ n, (∫⁻ x, f 0 x) - (∫⁻ x, f n x) := by
              have h_mono : ∀ n, ∀ x, f n x ≤ f 0 x := fun n x ↦ h_anti (Nat.zero_le n) x
              refine congrArg iSup <| funext fun n ↦ ?_
              exact lintegral_sub (h_meas 0) (h_meas n)
                (ne_top_of_le_ne_top h_fin (lintegral_mono (h_mono n))) (h_mono n)
        _ = (∫⁻ x, f 0 x) - (⨅ n, ∫⁻ x, f n x) := ENNReal.sub_iInf.symm

theorem limsup_lintegral_le {f : ℕ → ℝ → ℝ≥0∞}
    (g : ℝ → ℝ≥0∞) (hf_meas : ∀ n, Measurable (f n)) (h_bound : ∀ n, f n ≤ g)
    (h_fin : ∫⁻ x, g x ≠ ∞) :
    limsup (fun n ↦ ∫⁻ x, f n x) atTop ≤ ∫⁻ x, limsup (fun n ↦ f n x) atTop := by
  calc
    limsup (fun n ↦ ∫⁻ x, f n x) atTop =
        ⨅ n : ℕ, ⨆ i ≥ n, ∫⁻ x, f i x := limsup_eq_iInf_iSup_of_nat
    _ ≤ ⨅ n : ℕ, ∫⁻ x, ⨆ i ≥ n, f i x := by
          refine iInf_mono fun n ↦ ?_
          exact iSup₂_lintegral_le fun i _ x ↦ f i x
    _ = ∫⁻ x, ⨅ n : ℕ, ⨆ i ≥ n, f i x := by
          symm
          refine lintegral_iInf ?_ ?_ ?_
          · intro n
            exact .biSup {i : ℕ | n ≤ i} ({i : ℕ | n ≤ i}.to_countable) fun i _ ↦ hf_meas i
          · intro n m hnm x
            exact iSup_le_iSup_of_subset fun i hi ↦ le_trans hnm hi
          · refine ne_top_of_le_ne_top h_fin (lintegral_mono ?_)
            intro x
            exact iSup_le fun i ↦ iSup_le fun _ ↦ h_bound i x
    _ = ∫⁻ x, limsup (fun n ↦ f n x) atTop := by
          simp only [limsup_eq_iInf_iSup_of_nat]

theorem lintegral_liminf_le {f : ℕ → ℝ → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) :
    ∫⁻ x, liminf (fun n ↦ f n x) atTop ≤ liminf (fun n ↦ ∫⁻ x, f n x) atTop := by
  calc
    ∫⁻ x, liminf (fun n ↦ f n x) atTop =
        ∫⁻ x, ⨆ n : ℕ, ⨅ i ≥ n, f i x := by
          simp only [liminf_eq_iSup_iInf_of_nat]
    _ = ⨆ n : ℕ, ∫⁻ x, ⨅ i ≥ n, f i x := by
          exact lintegral_iSup
            (fun n ↦ .biInf {i : ℕ | n ≤ i} ({i : ℕ | n ≤ i}.to_countable) fun i _ ↦ h_meas i)
            (fun _ _ hnm _ ↦ iInf_le_iInf_of_subset fun _ hi ↦ le_trans hnm hi)
    _ ≤ ⨆ n : ℕ, (⨅ i ≥ n, ∫⁻ x, f i x) := iSup_mono fun _ ↦ le_iInf₂_lintegral _
    _ = liminf (fun n ↦ ∫⁻ x, f n x) atTop := Filter.liminf_eq_iSup_iInf_of_nat.symm

theorem tendsto_lintegral_of_dominated_convergence {F : ℕ → ℝ → ℝ≥0∞} {f : ℝ → ℝ≥0∞}
    (bound : ℝ → ℝ≥0∞) (hF_meas : ∀ n, Measurable (F n)) (h_bound : ∀ n, F n ≤ bound)
    (h_fin : ∫⁻ x, bound x ≠ ∞) (h_lim : ∀ x, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫⁻ x, F n x) atTop (𝓝 (∫⁻ x, f x)) :=
  tendsto_of_le_liminf_of_limsup_le
    (calc
      ∫⁻ x, f x = ∫⁻ x, liminf (fun n : ℕ ↦ F n x) atTop := by
        apply lintegral_congr
        intro x
        exact (h_lim x).liminf_eq.symm
      _ ≤ liminf (fun n ↦ ∫⁻ x, F n x) atTop := lintegral_liminf_le hF_meas)
    (calc
      limsup (fun n : ℕ ↦ ∫⁻ x, F n x) atTop ≤
          ∫⁻ x, limsup (fun n ↦ F n x) atTop := by
            exact limsup_lintegral_le _ hF_meas h_bound h_fin
      _ = ∫⁻ x, f x := by
          apply lintegral_congr
          intro x
          exact (h_lim x).limsup_eq)

end Real

end MTI
