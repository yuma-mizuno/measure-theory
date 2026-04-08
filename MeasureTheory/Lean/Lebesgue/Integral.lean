import MeasureTheory.Lean.Lebesgue.Lintegral

set_option autoImplicit false

noncomputable section

open Function ENNReal Topology NNReal Set Filter

namespace MTI

namespace Real

/-- The positive part of a real-valued function, regarded as an `ℝ≥0∞`-valued function. -/
def posPart (f : ℝ → ℝ) : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (f x)

/-- The negative part of a real-valued function, regarded as an `ℝ≥0∞`-valued function. -/
def negPart (f : ℝ → ℝ) : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (-f x)

/-- The sum of the positive and negative parts is the absolute value. -/
theorem posPart_add_negPart_eq_abs {f : ℝ → ℝ} (x : ℝ) :
    posPart f x + negPart f x = ENNReal.ofReal |f x| := by
  by_cases hx : 0 ≤ f x
  · have hneg : -f x ≤ 0 := by linarith
    simp [posPart, negPart, abs_of_nonneg hx, hneg]
  · have hx' : f x ≤ 0 := le_of_not_ge hx
    have hneg : 0 ≤ -f x := by linarith
    simp [posPart, negPart, abs_of_nonpos hx', hx']

theorem posPart_le_abs {f : ℝ → ℝ} (x : ℝ) :
    posPart f x ≤ ENNReal.ofReal |f x| := by
  calc
    posPart f x ≤ posPart f x + negPart f x := by
      exact le_add_of_nonneg_right (by simp)
    _ = ENNReal.ofReal |f x| := posPart_add_negPart_eq_abs (f := f) x

theorem negPart_le_abs {f : ℝ → ℝ} (x : ℝ) :
    negPart f x ≤ ENNReal.ofReal |f x| := by
  calc
    negPart f x ≤ posPart f x + negPart f x := by
      exact le_add_of_nonneg_left (by simp)
    _ = ENNReal.ofReal |f x| := posPart_add_negPart_eq_abs (f := f) x

/-- A real-valued function is the difference of its positive and negative parts. -/
theorem eq_posPart_sub_negPart {f : ℝ → ℝ} (x : ℝ) :
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

theorem abs_eq_posPart_add_negPart {f : ℝ → ℝ} (x : ℝ) :
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

theorem negPart_eq_zero_of_nonneg {f : ℝ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) :
    negPart f = fun _ ↦ 0 := by
  funext x
  have hneg : -f x ≤ 0 := by linarith [hf_nonneg x]
  simp [negPart, hneg]

@[simp] theorem posPart_neg {f : ℝ → ℝ} :
    posPart (fun x ↦ -f x) = negPart f := by
  funext x
  simp [posPart, negPart]

@[simp] theorem negPart_neg {f : ℝ → ℝ} :
    negPart (fun x ↦ -f x) = posPart f := by
  funext x
  simp [posPart, negPart]

/-- Measurability for real-valued functions on `ℝ`, expressed through superlevel sets. -/
def MeasurableFun (f : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, MeasurableSet {x | a ≤ f x}

theorem measurableFun_const (c : ℝ) : MeasurableFun fun _ : ℝ ↦ c := by
  intro a
  by_cases h : a ≤ c
  · simpa [h] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
  · simpa [h] using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))

theorem measurableSet_le_const {f : ℝ → ℝ} (hf : MeasurableFun f) (a : ℝ) :
    MeasurableSet {x | f x ≤ a} := by
  have hEq : {x | f x ≤ a} = (⋃ n : ℕ, {x | a + 1 / (n + 1 : ℝ) ≤ f x})ᶜ := by
    ext x
    constructor
    · intro hxa
      have hx : x ∉ ⋃ n : ℕ, {x | a + 1 / (n + 1 : ℝ) ≤ f x} := by
        intro hx
        rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
        have hxa' : f x ≤ a := by simpa using hxa
        have hn' : a + 1 / (n + 1 : ℝ) ≤ f x := by simpa using hn
        have hpos : 0 < (1 / (n + 1 : ℝ)) := by positivity
        linarith
      simpa using hx
    · intro hx
      have hx' : x ∉ ⋃ n : ℕ, {x | a + 1 / (n + 1 : ℝ) ≤ f x} := by
        simpa using hx
      by_contra hxa
      have hxa' : a < f x := lt_of_not_ge hxa
      have hpos : 0 < f x - a := sub_pos.mpr hxa'
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      have hnx : a + 1 / (n + 1 : ℝ) ≤ f x := by linarith
      exact hx' (Set.mem_iUnion.mpr ⟨n, hnx⟩)
  rw [hEq]
  exact (MeasurableSet.iUnion _ fun n ↦ hf (a + 1 / (n + 1 : ℝ))).compl

theorem measurableSet_lt_const {f : ℝ → ℝ} (hf : MeasurableFun f) (a : ℝ) :
    MeasurableSet {x | a < f x} := by
  have heq : {x | a < f x} = ⋃ n : ℕ, {x | a + 1 / (n + 1 : ℝ) ≤ f x} := by
    ext x
    constructor
    · intro hx
      have hpos : 0 < f x - a := sub_pos.mpr hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      have : a + 1 / (n + 1 : ℝ) ≤ f x := by
        linarith
      simpa using this
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨n, hn⟩
      have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
      have : a + 1 / (n + 1 : ℝ) ≤ f x := by simpa using hn
      exact lt_of_lt_of_le (by linarith) this
  rw [heq]
  exact MeasurableSet.iUnion _ fun n ↦ hf (a + 1 / (n + 1 : ℝ))

theorem measurableSet_iInter_countable {ι : Type} [Countable ι] {A : ι → Set ℝ}
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (⋂ i, A i) := by
  have hEq : (⋂ i, A i) = (⋃ i, (A i)ᶜ)ᶜ := by
    ext x
    simp
  rw [hEq]
  exact (MeasurableSet.iUnion_countable fun i ↦ (hA i).compl).compl

theorem setOf_le_eq_iInter_lt {f : ℝ → ℝ} (a : ℝ) :
    {x | a ≤ f x} = ⋂ k : ℕ, {x | a - 1 / (k + 1 : ℝ) < f x} := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.2 fun k ↦ ?_
    have hxa : a ≤ f x := by simpa using hx
    have : a - 1 / (k + 1 : ℝ) < f x := by
      have hpos : 0 < 1 / (k + 1 : ℝ) := by positivity
      linarith
    simpa using this
  · intro hx
    by_contra hxa
    have hxa' : f x < a := lt_of_not_ge hxa
    have hpos : 0 < a - f x := sub_pos.mpr hxa'
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    have hxk : a - 1 / (k + 1 : ℝ) < f x := by
      exact Set.mem_iInter.1 hx k
    have : f x < a - 1 / (k + 1 : ℝ) := by
      have hlt : 1 / (k + 1 : ℝ) < a - f x := by simpa using hk
      linarith
    exact not_lt_of_gt this hxk

theorem setOf_le_eq_iInter_iUnion_iInter {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (h_lim : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) (a : ℝ) :
    {x | a ≤ f x} =
      ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n ∈ Set.Ici N, {x | a - 1 / (k + 1 : ℝ) ≤ F n x} := by
  ext x
  constructor
  · intro hx
    refine mem_iInter.2 fun k ↦ ?_
    have hxa : a ≤ f x := by simpa using hx
    have hak : a - 1 / (k + 1 : ℝ) < f x := by
      have hpos : 0 < 1 / (k + 1 : ℝ) := by positivity
      linarith
    have hmem : {y : ℝ | a - 1 / (k + 1 : ℝ) < y} ∈ nhds (f x) := Ioi_mem_nhds hak
    rcases mem_atTop_sets.1 ((h_lim x) hmem) with ⟨N, hN⟩
    refine mem_iUnion.2 ⟨N, mem_iInter.2 fun n ↦ mem_iInter.2 fun hn ↦ ?_⟩
    have hn' : a - 1 / (k + 1 : ℝ) < F n x := by
      simpa [Set.mem_Ici] using hN n hn
    exact hn'.le
  · intro hx
    by_contra hxa
    have hxa' : f x < a := lt_of_not_ge hxa
    have hpos : 0 < a - f x := sub_pos.mpr hxa'
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    rcases mem_iInter.1 hx k with hxk
    rcases mem_iUnion.1 hxk with ⟨N, hN⟩
    have hak : f x < a - 1 / (k + 1 : ℝ) := by
      have hlt : 1 / (k + 1 : ℝ) < a - f x := by simpa using hk
      linarith
    have hmem : {y : ℝ | y < a - 1 / (k + 1 : ℝ)} ∈ nhds (f x) := Iio_mem_nhds hak
    rcases mem_atTop_sets.1 ((h_lim x) hmem) with ⟨M, hM⟩
    let n : ℕ := max N M
    have hnN : n ∈ Set.Ici N := by
      simp [n, Set.mem_Ici]
    have hn₁ : a - 1 / (k + 1 : ℝ) ≤ F n x := by
      exact mem_iInter.1 (mem_iInter.1 hN n) hnN
    have hn₂ : F n x < a - 1 / (k + 1 : ℝ) := by
      have : n ∈ {n | F n x < a - 1 / (k + 1 : ℝ)} := hM n (by simp [n])
      simpa using this
    exact hn₂.not_ge hn₁

theorem measurableSet_iUnion_iInter_Ici {F : ℕ → ℝ → ℝ}
    (hF_meas : ∀ n, MeasurableFun (F n)) (a : ℝ) (k : ℕ) :
    MeasurableSet (⋃ N : ℕ, ⋂ n ∈ Set.Ici N, {x | a - 1 / (k + 1 : ℝ) ≤ F n x}) := by
  let s : ℕ → Set ℝ := fun N => ⋂ n : Set.Ici N, {x | a - 1 / (k + 1 : ℝ) ≤ F n.1 x}
  have hN : ∀ N : ℕ, MeasurableSet (s N) := by
    intro N
    have hs : MeasurableSet (⋂ n : Set.Ici N, {x | a - 1 / (k + 1 : ℝ) ≤ F n.1 x}) := by
      exact measurableSet_iInter_countable fun n : Set.Ici N =>
        hF_meas n.1 (a - 1 / (k + 1 : ℝ))
    simpa [s] using hs
  have hs : MeasurableSet (⋃ N : ℕ, s N) := MeasurableSet.iUnion _ hN
  simpa [s, biInter_eq_iInter] using hs

theorem measurableFun_of_tendsto {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF_meas : ∀ n, MeasurableFun (F n))
    (h_lim : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    MeasurableFun f := by
  intro a
  rw [setOf_le_eq_iInter_iUnion_iInter h_lim a]
  exact MeasurableSet.iInter fun k ↦ measurableSet_iUnion_iInter_Ici hF_meas a k

theorem MeasurableFun.const_mul_nonneg {f : ℝ → ℝ} (hf : MeasurableFun f) {c : ℝ}
    (hc : 0 ≤ c) : MeasurableFun (fun x ↦ c * f x) := by
  by_cases hc0 : c = 0
  · simpa [hc0] using (measurableFun_const 0)
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (by simpa [eq_comm] using hc0)
    intro a
    have hEq : {x | a ≤ c * f x} = {x | a / c ≤ f x} := by
      ext x
      constructor
      · intro hx
        have hx' : a ≤ c * f x := by simpa using hx
        have : a / c ≤ f x := by
          exact (div_le_iff₀' hc_pos).2 hx'
        simpa using this
      · intro hx
        have hx' : a / c ≤ f x := by simpa using hx
        have : a ≤ c * f x := (div_le_iff₀' hc_pos).1 hx'
        simpa using this
    rw [hEq]
    exact hf (a / c)

theorem MeasurableFun.neg {f : ℝ → ℝ} (hf : MeasurableFun f) :
    MeasurableFun (fun x ↦ -f x) := by
  intro a
  have hEq : {x | a ≤ -f x} = {x | f x ≤ -a} := by
    ext x
    constructor
    · intro hx
      have hx' : a ≤ -f x := by simpa using hx
      simpa using (show f x ≤ -a by linarith)
    · intro hx
      have hx' : f x ≤ -a := by simpa using hx
      simpa using (show a ≤ -f x by linarith)
  rw [hEq]
  exact measurableSet_le_const hf (-a)

theorem MeasurableFun.const_mul {f : ℝ → ℝ} (hf : MeasurableFun f) (c : ℝ) :
    MeasurableFun (fun x ↦ c * f x) := by
  by_cases hc : 0 ≤ c
  · exact hf.const_mul_nonneg hc
  · have hneg : 0 ≤ -c := by linarith
    have hscaled : MeasurableFun (fun x ↦ (-c) * f x) := hf.const_mul_nonneg hneg
    intro a
    have hEq : {x | a ≤ c * f x} = {x | (-c) * f x ≤ -a} := by
      ext x
      constructor
      · intro hx
        have hx' : a ≤ c * f x := by simpa using hx
        have : (-c) * f x ≤ -a := by linarith
        simpa using this
      · intro hx
        have hx' : (-c) * f x ≤ -a := by simpa using hx
        have : a ≤ c * f x := by linarith
        simpa using this
    rw [hEq]
    exact measurableSet_le_const hscaled (-a)

theorem measurable_posPart {f : ℝ → ℝ} (hf : MeasurableFun f) :
    Measurable (posPart f) := by
  intro a
  by_cases ha_top : a = ∞
  · have hEq : {x | a ≤ posPart f x} = (∅ : Set ℝ) := by
      ext x
      simp [ha_top, posPart]
    rw [hEq]
    exact MeasurableSet.empty
  · by_cases ha_zero : a = 0
    · simpa [ha_zero, posPart] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
    · have hEq : {x | a ≤ posPart f x} = {x | a.toReal ≤ f x} := by
        ext x
        constructor
        · intro hax
          by_cases hfx : 0 ≤ f x
          · exact (ENNReal.le_ofReal_iff_toReal_le ha_top hfx).1 <| by simpa [posPart] using hax
          · have ha_pos : (0 : ℝ≥0∞) < a := bot_lt_iff_ne_bot.mpr ha_zero
            have hnot : ¬ a ≤ posPart f x := by
              rw [posPart, ENNReal.ofReal_of_nonpos (le_of_not_ge hfx)]
              exact not_le_of_gt ha_pos
            exact (hnot hax).elim
        · intro hax
          have hfx : 0 ≤ f x := le_trans ENNReal.toReal_nonneg hax
          exact (ENNReal.le_ofReal_iff_toReal_le ha_top hfx).2 hax
      rw [hEq]
      exact hf a.toReal

theorem measurable_negPart {f : ℝ → ℝ} (hf : MeasurableFun f) :
    Measurable (negPart f) := by
  simpa [posPart_neg] using measurable_posPart hf.neg

theorem measurable_abs {f : ℝ → ℝ} (hf : MeasurableFun f) :
    Measurable (fun x ↦ ENNReal.ofReal |f x|) := by
  intro a
  by_cases ha_top : a = ∞
  · have hEq : {x | a ≤ ENNReal.ofReal |f x|} = (∅ : Set ℝ) := by
      ext x
      simp [ha_top]
    rw [hEq]
    exact MeasurableSet.empty
  · by_cases ha_zero : a = 0
    · simpa [ha_zero] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
    · have hEq :
          {x | a ≤ ENNReal.ofReal |f x|} = {x | a.toReal ≤ f x} ∪ {x | f x ≤ -a.toReal} := by
        ext x
        constructor
        · intro hax
          have hax' : a.toReal ≤ |f x| :=
            (ENNReal.le_ofReal_iff_toReal_le ha_top (abs_nonneg _)).1 <| by simpa using hax
          by_cases hfx : 0 ≤ f x
          · left
            simpa [abs_of_nonneg hfx] using hax'
          · right
            have hxle : f x ≤ 0 := le_of_not_ge hfx
            rw [abs_of_nonpos hxle] at hax'
            have : f x ≤ -a.toReal := by linarith
            simpa using this
        · intro hx
          rcases hx with hsup | hsub
          · have hfx : 0 ≤ f x := le_trans ENNReal.toReal_nonneg hsup
            exact (ENNReal.le_ofReal_iff_toReal_le ha_top (abs_nonneg _)).2 <| by
              simpa [abs_of_nonneg hfx] using hsup
          · have hfx : f x ≤ 0 := by
              have hnonneg : 0 ≤ a.toReal := ENNReal.toReal_nonneg
              have hsub' : f x ≤ -a.toReal := by simpa using hsub
              linarith
            have hax' : a.toReal ≤ |f x| := by
              rw [abs_of_nonpos hfx]
              have hsub' : f x ≤ -a.toReal := by simpa using hsub
              linarith
            exact (ENNReal.le_ofReal_iff_toReal_le ha_top (abs_nonneg _)).2 hax'
      rw [hEq]
      exact (hf a.toReal).union (measurableSet_le_const hf (-a.toReal))

theorem posPart_add_add_negPart_eq_negPart_add_posPart {f g : ℝ → ℝ} (x : ℝ) :
    posPart (fun x ↦ f x + g x) x + negPart f x + negPart g x =
      negPart (fun x ↦ f x + g x) x + posPart f x + posPart g x := by
  have hL₁ : posPart (fun x ↦ f x + g x) x ≠ ∞ := by simp [posPart]
  have hL₂ : negPart f x ≠ ∞ := by simp [negPart]
  have hL₃ : negPart g x ≠ ∞ := by simp [negPart]
  have hR₁ : negPart (fun x ↦ f x + g x) x ≠ ∞ := by simp [negPart]
  have hR₂ : posPart f x ≠ ∞ := by simp [posPart]
  have hR₃ : posPart g x ≠ ∞ := by simp [posPart]
  have hL : posPart (fun x ↦ f x + g x) x + negPart f x + negPart g x ≠ ∞ := by
    rw [add_assoc]
    exact add_ne_top.mpr ⟨hL₁, add_ne_top.mpr ⟨hL₂, hL₃⟩⟩
  have hR : negPart (fun x ↦ f x + g x) x + posPart f x + posPart g x ≠ ∞ := by
    rw [add_assoc]
    exact add_ne_top.mpr ⟨hR₁, add_ne_top.mpr ⟨hR₂, hR₃⟩⟩
  apply (ENNReal.toReal_eq_toReal_iff' hL hR).mp
  rw [add_assoc, add_assoc]
  rw [ENNReal.toReal_add hL₁ (add_ne_top.mpr ⟨hL₂, hL₃⟩)]
  rw [ENNReal.toReal_add hL₂ hL₃]
  rw [ENNReal.toReal_add hR₁ (add_ne_top.mpr ⟨hR₂, hR₃⟩)]
  rw [ENNReal.toReal_add hR₂ hR₃]
  linarith [eq_posPart_sub_negPart (f := f) x, eq_posPart_sub_negPart (f := g) x,
    eq_posPart_sub_negPart (f := fun y ↦ f y + g y) x]

/-- A real-valued function has finite integral if the lower integral of its absolute value is
finite. -/
def HasFiniteIntegral (f : ℝ → ℝ) : Prop :=
  ∫⁻ x, ENNReal.ofReal |f x| < ∞

theorem hasFiniteIntegral_iff {f : ℝ → ℝ} :
    HasFiniteIntegral f ↔ ∫⁻ x, ENNReal.ofReal |f x| < ∞ :=
  Iff.rfl

theorem HasFiniteIntegral.ne_top {f : ℝ → ℝ} (hf : HasFiniteIntegral f) :
    ∫⁻ x, ENNReal.ofReal |f x| ≠ ∞ :=
  ne_of_lt hf

theorem hasFiniteIntegral_of_ne_top {f : ℝ → ℝ}
    (hf : ∫⁻ x, ENNReal.ofReal |f x| ≠ ∞) :
    HasFiniteIntegral f :=
  lt_of_le_of_ne le_top hf

theorem HasFiniteIntegral.pos_ne_top {f : ℝ → ℝ} (hf : HasFiniteIntegral f) :
    ∫⁻ x, posPart f x ≠ ∞ := by
  refine ne_top_of_le_ne_top hf.ne_top ?_
  exact lintegral_mono fun x ↦ posPart_le_abs (f := f) x

theorem HasFiniteIntegral.neg_ne_top {f : ℝ → ℝ} (hf : HasFiniteIntegral f) :
    ∫⁻ x, negPart f x ≠ ∞ := by
  refine ne_top_of_le_ne_top hf.ne_top ?_
  exact lintegral_mono fun x ↦ negPart_le_abs (f := f) x

/-- A real-valued function on `ℝ` is integrable if it is measurable and the lower integral of its
absolute value is finite. -/
structure Integrable (f : ℝ → ℝ) : Prop where
  measurable : MeasurableFun f
  hasFiniteIntegral : HasFiniteIntegral f

theorem integrable_congr {f g : ℝ → ℝ} (hfg : ∀ x, f x = g x) :
    Integrable f ↔ Integrable g := by
  have hpos : posPart f = posPart g := by
    funext x
    simp [posPart, hfg x]
  have hneg : negPart f = negPart g := by
    funext x
    simp [negPart, hfg x]
  have habs : (fun x ↦ ENNReal.ofReal |f x|) = fun x ↦ ENNReal.ofReal |g x| := by
    funext x
    simp [hfg x]
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro a
      simpa [hfg] using hf.measurable a
    simpa [HasFiniteIntegral, habs] using hf.hasFiniteIntegral
  · intro hg
    refine ⟨?_, ?_⟩
    · intro a
      simpa [hfg] using hg.measurable a
    simpa [HasFiniteIntegral, habs] using hg.hasFiniteIntegral

theorem Integrable.posPart_ne_top {f : ℝ → ℝ} (hf : Integrable f) :
    ∫⁻ x, posPart f x ≠ ∞ :=
  hf.hasFiniteIntegral.pos_ne_top

theorem Integrable.negPart_ne_top {f : ℝ → ℝ} (hf : Integrable f) :
    ∫⁻ x, negPart f x ≠ ∞ :=
  hf.hasFiniteIntegral.neg_ne_top

theorem Integrable.neg {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (fun x ↦ -f x) := by
  refine ⟨hf.measurable.neg, ?_⟩
  refine hasFiniteIntegral_of_ne_top ?_
  simpa [HasFiniteIntegral] using hf.hasFiniteIntegral.ne_top

theorem Integrable.const_mul {f : ℝ → ℝ} (hf : Integrable f) (c : ℝ) :
    Integrable (fun x ↦ c * f x) := by
  refine ⟨hf.measurable.const_mul c, ?_⟩
  refine hasFiniteIntegral_of_ne_top ?_
  calc
    ∫⁻ x, ENNReal.ofReal |c * f x|
        = ∫⁻ x, ENNReal.ofReal |c| * ENNReal.ofReal |f x| := by
      apply lintegral_congr
      intro x
      rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
    _ = ENNReal.ofReal |c| * ∫⁻ x, ENNReal.ofReal |f x| := by
      rw [lintegral_const_mul _ (measurable_abs hf.measurable)]
    _ ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.hasFiniteIntegral.ne_top

theorem integrable_zero : Integrable (fun _ : ℝ ↦ (0 : ℝ)) := by
  refine ⟨measurableFun_const 0, ?_⟩
  simpa [HasFiniteIntegral] using (show ∫⁻ x, (0 : ℝ≥0∞) < ∞ by
    rw [lintegral_zero]
    simp)

theorem integrable_of_nonneg {f : ℝ → ℝ} (hf_meas : MeasurableFun f)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_fin : ∫⁻ x, ENNReal.ofReal (f x) < ∞) :
    Integrable f := by
  have habs : (fun x ↦ ENNReal.ofReal |f x|) = fun x ↦ ENNReal.ofReal (f x) := by
    funext x
    simp [abs_of_nonneg (hf_nonneg x)]
  refine ⟨hf_meas, ?_⟩
  simpa [HasFiniteIntegral, habs] using hf_fin

/-- The Lebesgue integral of a real-valued function on `ℝ`. -/
noncomputable def integral (f : ℝ → ℝ) : ℝ := by
  classical
  exact
    if h : Integrable f then
      (∫⁻ x, posPart f x).toReal - (∫⁻ x, negPart f x).toReal
    else
      0

notation3 (priority := high) "∫ "(...)", " r:60:(scoped f => f) => integral r

theorem integral_congr {f g : ℝ → ℝ} (hfg : ∀ x, f x = g x) :
    ∫ x, f x = ∫ x, g x := by
  by_cases hf : Integrable f
  · have hg : Integrable g := (integrable_congr (f := f) (g := g) hfg).1 hf
    rw [integral, dif_pos hf, integral, dif_pos hg]
    have hpos : ∫⁻ x, posPart f x = ∫⁻ x, posPart g x := by
      apply lintegral_congr
      intro x
      simp [posPart, hfg x]
    have hneg : ∫⁻ x, negPart f x = ∫⁻ x, negPart g x := by
      apply lintegral_congr
      intro x
      simp [negPart, hfg x]
    rw [hpos, hneg]
  · have hg : ¬ Integrable g := by
      intro hg
      exact hf ((integrable_congr (f := f) (g := g) hfg).2 hg)
    rw [integral, dif_neg hf, integral, dif_neg hg]

theorem integral_eq_lintegral_posPart_sub_lintegral_negPart {f : ℝ → ℝ} (hf : Integrable f) :
    ∫ x, f x = (∫⁻ x, posPart f x).toReal - (∫⁻ x, negPart f x).toReal := by
  rw [integral, dif_pos hf]

theorem integral_eq_zero_of_not_integrable {f : ℝ → ℝ} (hf_not : ¬ Integrable f) :
    ∫ x, f x = 0 := by
  rw [integral, dif_neg hf_not]

theorem integral_eq_lintegral_of_nonneg {f : ℝ → ℝ} (hf_meas : MeasurableFun f)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    ∫ x, f x = (∫⁻ x, ENNReal.ofReal (f x)).toReal := by
  by_cases hfin : ∫⁻ x, ENNReal.ofReal (f x) = ∞
  · have hf_not : ¬ Integrable f := by
      intro hf
      exact hf.posPart_ne_top (by simpa [posPart, hf_nonneg] using hfin)
    rw [integral_eq_zero_of_not_integrable hf_not, hfin, ENNReal.toReal_top]
  · have hf_int : Integrable f := by
      exact integrable_of_nonneg hf_meas hf_nonneg (lt_of_le_of_ne le_top hfin)
    rw [integral_eq_lintegral_posPart_sub_lintegral_negPart hf_int]
    rw [negPart_eq_zero_of_nonneg hf_nonneg, lintegral_zero, ENNReal.toReal_zero, sub_zero]
    apply congrArg ENNReal.toReal
    apply lintegral_congr
    intro x
    simp [posPart]

theorem integral_nonneg {f : ℝ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) :
    0 ≤ ∫ x, f x := by
  by_cases hf : Integrable f
  · rw [integral_eq_lintegral_of_nonneg hf.measurable hf_nonneg]
    exact ENNReal.toReal_nonneg
  · rw [integral_eq_zero_of_not_integrable hf]

theorem integral_zero : (∫ _x, (0 : ℝ)) = 0 := by
  rw [integral_eq_lintegral_posPart_sub_lintegral_negPart integrable_zero]
  have hpos : posPart (fun _ : ℝ ↦ (0 : ℝ)) = fun _ ↦ (0 : ℝ≥0∞) := by
    funext x
    simp [posPart]
  have hneg : negPart (fun _ : ℝ ↦ (0 : ℝ)) = fun _ ↦ (0 : ℝ≥0∞) := by
    funext x
    simp [negPart]
  simp [hpos, hneg, lintegral_zero]

theorem integral_neg {f : ℝ → ℝ} :
    ∫ x, -f x = -(∫ x, f x) := by
  by_cases hf : Integrable f
  · rw [integral_eq_lintegral_posPart_sub_lintegral_negPart hf,
      integral_eq_lintegral_posPart_sub_lintegral_negPart hf.neg]
    rw [posPart_neg, negPart_neg]
    ring
  · have hneg : ¬ Integrable (fun x ↦ -f x) := by
      intro h
      have h' : Integrable (fun x ↦ -(-f x)) := h.neg
      have h'' : Integrable f := by
        exact (integrable_congr (f := fun x ↦ -(-f x)) (g := f) (by intro x; ring)).1 h'
      exact hf h''
    rw [integral_eq_zero_of_not_integrable hneg, integral_eq_zero_of_not_integrable hf]
    simp

theorem posPart_const_mul_of_nonneg {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    posPart (fun x ↦ c * f x) = fun x ↦ ENNReal.ofReal c * posPart f x := by
  funext x
  rw [posPart, posPart, ENNReal.ofReal_mul hc]

theorem negPart_const_mul_of_nonneg {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    negPart (fun x ↦ c * f x) = fun x ↦ ENNReal.ofReal c * negPart f x := by
  funext x
  have hmul : -(c * f x) = c * (-f x) := by ring
  rw [negPart, hmul, negPart, ENNReal.ofReal_mul hc]

theorem integral_const_mul_of_nonneg {f : ℝ → ℝ} (hf : Integrable f) {c : ℝ} (hc : 0 ≤ c) :
    ∫ x, c * f x = c * ∫ x, f x := by
  rw [integral_eq_lintegral_posPart_sub_lintegral_negPart (hf.const_mul c),
    integral_eq_lintegral_posPart_sub_lintegral_negPart hf]
  rw [posPart_const_mul_of_nonneg hc, negPart_const_mul_of_nonneg hc]
  rw [lintegral_const_mul _ (measurable_posPart hf.measurable)]
  rw [lintegral_const_mul _ (measurable_negPart hf.measurable)]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  ring

theorem integral_const_mul (c : ℝ) {f : ℝ → ℝ} (hf : Integrable f) :
    ∫ x, c * f x = c * ∫ x, f x := by
  by_cases hc : 0 ≤ c
  · exact integral_const_mul_of_nonneg hf hc
  · have hc' : 0 ≤ -c := by linarith
    calc
      integral (fun x ↦ c * f x) = integral (fun x ↦ -((-c) * f x)) := by
        apply integral_congr
        intro x
        ring
      _ = -integral (fun x ↦ (-c) * f x) := by
        rw [integral_neg]
      _ = -((-c) * integral f) := by
        rw [integral_const_mul_of_nonneg hf hc']
      _ = c * integral f := by
        ring

theorem integral_add_eq_integral_add {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hfg : Integrable (fun x ↦ f x + g x)) :
    ∫ x, f x + g x = (∫ x, f x) + ∫ x, g x := by
  have hlin :
      (∫⁻ x, posPart (fun x ↦ f x + g x) x) + (∫⁻ x, negPart f x) + (∫⁻ x, negPart g x) =
        (∫⁻ x, negPart (fun x ↦ f x + g x) x) +
          (∫⁻ x, posPart f x) + ∫⁻ x, posPart g x := by
    rw [add_assoc, add_assoc]
    rw [← lintegral_add (measurable_negPart hf.measurable) (measurable_negPart hg.measurable)]
    rw [← lintegral_add (measurable_posPart hfg.measurable)
      ((measurable_negPart hf.measurable).add (measurable_negPart hg.measurable))]
    rw [← lintegral_add (measurable_posPart hf.measurable) (measurable_posPart hg.measurable)]
    rw [← lintegral_add (measurable_negPart hfg.measurable)
      ((measurable_posPart hf.measurable).add (measurable_posPart hg.measurable))]
    apply lintegral_congr
    intro x
    simpa [add_assoc] using posPart_add_add_negPart_eq_negPart_add_posPart (f := f) (g := g) x
  have hL₁ : ∫⁻ x, posPart (fun x ↦ f x + g x) x ≠ ∞ := hfg.posPart_ne_top
  have hL₂ : ∫⁻ x, negPart f x ≠ ∞ := hf.negPart_ne_top
  have hL₃ : ∫⁻ x, negPart g x ≠ ∞ := hg.negPart_ne_top
  have hR₁ : ∫⁻ x, negPart (fun x ↦ f x + g x) x ≠ ∞ := hfg.negPart_ne_top
  have hR₂ : ∫⁻ x, posPart f x ≠ ∞ := hf.posPart_ne_top
  have hR₃ : ∫⁻ x, posPart g x ≠ ∞ := hg.posPart_ne_top
  have hreal := congrArg ENNReal.toReal hlin
  rw [add_assoc, add_assoc] at hreal
  rw [ENNReal.toReal_add hL₁ (add_ne_top.mpr ⟨hL₂, hL₃⟩)] at hreal
  rw [ENNReal.toReal_add hL₂ hL₃] at hreal
  rw [ENNReal.toReal_add hR₁ (add_ne_top.mpr ⟨hR₂, hR₃⟩)] at hreal
  rw [ENNReal.toReal_add hR₂ hR₃] at hreal
  rw [integral_eq_lintegral_posPart_sub_lintegral_negPart hf,
    integral_eq_lintegral_posPart_sub_lintegral_negPart hg,
    integral_eq_lintegral_posPart_sub_lintegral_negPart hfg]
  linarith

theorem integral_sub_eq_integral_sub {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hfg : Integrable (fun x ↦ f x - g x)) :
    ∫ x, f x - g x = (∫ x, f x) - ∫ x, g x := by
  have hadd : Integrable (fun x ↦ f x + -g x) := (integrable_congr (f := fun x ↦ f x - g x)
    (g := fun x ↦ f x + -g x) (fun x ↦ by ring)).mp hfg
  calc
    integral (fun x ↦ f x - g x) = integral (fun x ↦ f x + -g x) := by
      apply integral_congr
      intro x
      ring
    _ = integral f + integral (fun x ↦ -g x) := integral_add_eq_integral_add hf hg.neg hadd
    _ = integral f - integral g := by
      rw [integral_neg]
      ring

theorem abs_integral_le_lintegral_abs {f : ℝ → ℝ} (hf : Integrable f) :
    |∫ x, f x| ≤ (∫⁻ x, ENNReal.ofReal |f x|).toReal := by
  have habs :
      ∫⁻ x, ENNReal.ofReal |f x| =
        (∫⁻ x, posPart f x) + ∫⁻ x, negPart f x := by
    calc
      ∫⁻ x, ENNReal.ofReal |f x| =
          ∫⁻ x, posPart f x + negPart f x := by
            apply lintegral_congr
            intro x
            symm
            exact posPart_add_negPart_eq_abs (f := f) x
      _ = (∫⁻ x, posPart f x) + ∫⁻ x, negPart f x := by
            exact lintegral_add
              (measurable_posPart hf.measurable)
              (measurable_negPart hf.measurable)
  calc
    |∫ x, f x| =
        |(∫⁻ x, posPart f x).toReal - (∫⁻ x, negPart f x).toReal| := by
          rw [integral_eq_lintegral_posPart_sub_lintegral_negPart hf]
    _ ≤ |(∫⁻ x, posPart f x).toReal| + |(∫⁻ x, negPart f x).toReal| := by
      simpa using abs_sub_le (∫⁻ x, posPart f x).toReal 0 (∫⁻ x, negPart f x).toReal
    _ = (∫⁻ x, posPart f x).toReal + (∫⁻ x, negPart f x).toReal := by
      rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = (∫⁻ x, ENNReal.ofReal |f x|).toReal := by
      rw [habs, ENNReal.toReal_add hf.posPart_ne_top hf.negPart_ne_top]

/-- Dominated convergence theorem for real-valued measurable functions on `ℝ`. -/
theorem tendsto_integral_of_dominated_convergence
    {F : ℕ → ℝ → ℝ} {f bound : ℝ → ℝ}
    (hF_meas : ∀ n, MeasurableFun (F n)) (h_bound_int : Integrable bound)
    (h_bound : ∀ n x, |F n x| ≤ bound x)
    (h_lim : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x) atTop (nhds (∫ x, f x)) := by
  have h_bound_nonneg : ∀ x, 0 ≤ bound x := by
    intro x
    exact le_trans (abs_nonneg (F 0 x)) (h_bound 0 x)
  have h_bound_ne_top : ∫⁻ x, ENNReal.ofReal (bound x) ≠ ∞ := by
    have habs : (fun x ↦ ENNReal.ofReal |bound x|) = fun x ↦ ENNReal.ofReal (bound x) := by
      funext x
      simp [abs_of_nonneg (h_bound_nonneg x)]
    simpa [HasFiniteIntegral, habs] using h_bound_int.hasFiniteIntegral.ne_top
  have hf_meas : MeasurableFun f := measurableFun_of_tendsto hF_meas h_lim
  have h_abs_f_le : ∀ x, |f x| ≤ bound x := by
    intro x
    have h_closed : IsClosed (Set.Icc (-bound x) (bound x)) := isClosed_Icc
    have h_mem : ∀ᶠ n in atTop, F n x ∈ Set.Icc (-bound x) (bound x) := by
      refine Filter.Eventually.of_forall fun n ↦ ?_
      exact abs_le.mp (h_bound n x)
    have hf_mem : f x ∈ Set.Icc (-bound x) (bound x) :=
      h_closed.mem_of_tendsto (h_lim x) h_mem
    exact abs_le.mpr hf_mem
  have hF_int : ∀ n, Integrable (F n) := by
    intro n
    refine ⟨hF_meas n, ?_⟩
    refine hasFiniteIntegral_of_ne_top ?_
    refine ne_top_of_le_ne_top h_bound_ne_top ?_
    exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (h_bound n x)
  have hf_int : Integrable f := by
    refine ⟨hf_meas, ?_⟩
    refine hasFiniteIntegral_of_ne_top ?_
    refine ne_top_of_le_ne_top h_bound_ne_top ?_
    exact lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (h_abs_f_le x)
  have h_pos_lim : ∀ x, Tendsto (fun n ↦ posPart (F n) x) atTop (nhds (posPart f x)) := by
    intro x
    simpa [posPart] using ((ENNReal.continuous_ofReal.tendsto (f x)).comp (h_lim x))
  have h_neg_lim : ∀ x, Tendsto (fun n ↦ negPart (F n) x) atTop (nhds (negPart f x)) := by
    intro x
    simpa [negPart] using
      (((ENNReal.continuous_ofReal.comp continuous_neg).tendsto (f x)).comp (h_lim x))
  have h_pos_tendsto :
      Tendsto (fun n ↦ ∫⁻ x, posPart (F n) x) atTop (nhds (∫⁻ x, posPart f x)) := by
    exact tendsto_lintegral_of_dominated_convergence
      (fun x ↦ ENNReal.ofReal (bound x))
      (fun n ↦ measurable_posPart (hF_meas n))
      (fun n x ↦
        le_trans (posPart_le_abs (f := F n) x) (ENNReal.ofReal_le_ofReal (h_bound n x)))
      h_bound_ne_top
      h_pos_lim
  have h_neg_tendsto :
      Tendsto (fun n ↦ ∫⁻ x, negPart (F n) x) atTop (nhds (∫⁻ x, negPart f x)) := by
    exact tendsto_lintegral_of_dominated_convergence
      (fun x ↦ ENNReal.ofReal (bound x))
      (fun n ↦ measurable_negPart (hF_meas n))
      (fun n x ↦
        le_trans (negPart_le_abs (f := F n) x) (ENNReal.ofReal_le_ofReal (h_bound n x)))
      h_bound_ne_top
      h_neg_lim
  have h_pos_toReal :
      Tendsto (fun n ↦ (∫⁻ x, posPart (F n) x).toReal) atTop
        (nhds ((∫⁻ x, posPart f x).toReal)) := by
    exact (ENNReal.tendsto_toReal hf_int.posPart_ne_top).comp h_pos_tendsto
  have h_neg_toReal :
      Tendsto (fun n ↦ (∫⁻ x, negPart (F n) x).toReal) atTop
        (nhds ((∫⁻ x, negPart f x).toReal)) := by
    exact (ENNReal.tendsto_toReal hf_int.negPart_ne_top).comp h_neg_tendsto
  rw [integral_eq_lintegral_posPart_sub_lintegral_negPart hf_int]
  have hF_eq :
      (fun n ↦ ∫ x, F n x) =
        fun n ↦ (∫⁻ x, posPart (F n) x).toReal - (∫⁻ x, negPart (F n) x).toReal := by
    funext n
    rw [integral_eq_lintegral_posPart_sub_lintegral_negPart (hF_int n)]
  rw [hF_eq]
  exact h_pos_toReal.sub h_neg_toReal

end Real

end MTI
