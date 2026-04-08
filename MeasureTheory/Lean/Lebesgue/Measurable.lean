import MeasureTheory.Lean.Lebesgue.SimpleFunc

set_option autoImplicit false

noncomputable section

open Function ENNReal NNReal Topology Set

namespace MTI

namespace Real

open SimpleFunc

/-- Measurability for nonnegative functions on `ℝ`, expressed through superlevel sets. -/
def Measurable (f : ℝ → ℝ≥0∞) : Prop :=
  ∀ a : ℝ≥0∞, MeasurableSet {x | a ≤ f x}

theorem measurable_const (c : ℝ≥0∞) : Measurable fun _ : ℝ ↦ c := by
  intro a
  by_cases h : a ≤ c
  · simpa [h] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
  · simpa [h] using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))

theorem measurableSet_lt {f : ℝ → ℝ≥0∞} (hf : Measurable f) (a : ℝ≥0∞) :
    MeasurableSet {x | a < f x} := by
  let S : Type := {q : ℚ // 0 ≤ q ∧ a < (Real.toNNReal q : ℝ≥0∞)}
  have heq :
      {x | a < f x} = ⋃ q : S, {x | (Real.toNNReal q.1 : ℝ≥0∞) ≤ f x} := by
    ext x
    constructor
    · intro hx
      rcases ENNReal.lt_iff_exists_rat_btwn.1 hx with ⟨q, hq0, haq, hqf⟩
      exact mem_iUnion.2 ⟨⟨q, hq0, haq⟩, hqf.le⟩
    · intro hx
      rcases mem_iUnion.1 hx with ⟨q, hxq⟩
      exact lt_of_lt_of_le q.2.2 hxq
  rw [heq]
  exact MeasurableSet.iUnion_countable fun q ↦ hf (Real.toNNReal q.1 : ℝ≥0∞)

private theorem measurableSet_iInter_countable {ι : Type*} [Countable ι] {A : ι → Set ℝ}
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (⋂ i, A i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [MeasurableSet.univ]
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iInter_congr_of_surjective e he fun _ ↦ rfl]
    exact MeasurableSet.iInter fun n ↦ hA (e n)

theorem Measurable.of_Ioi {f : ℝ → ℝ≥0∞}
    (hf : ∀ a : ℝ≥0∞, MeasurableSet {x | a < f x}) : Measurable f := by
  intro a
  by_cases ha0 : a = 0
  · simpa [ha0] using MeasurableSet.univ
  · let S : Type := {q : ℚ // 0 ≤ q ∧ (Real.toNNReal q : ℝ≥0∞) < a}
    letI : Countable S := inferInstance
    have heq : {x | a ≤ f x} = ⋂ q : S, {x | (Real.toNNReal q.1 : ℝ≥0∞) < f x} := by
      ext x
      constructor
      · intro hx
        refine mem_iInter.2 fun q ↦ ?_
        exact lt_of_lt_of_le q.2.2 hx
      · intro hx
        by_contra hxa
        have hlt : f x < a := lt_of_not_ge hxa
        rcases ENNReal.lt_iff_exists_rat_btwn.1 hlt with ⟨q, hq0, hfxq, hqa⟩
        have hxn : (Real.toNNReal q : ℝ≥0∞) < f x := by
          simpa using mem_iInter.1 hx ⟨q, hq0, hqa⟩
        exact (not_lt_of_ge hfxq.le) hxn
    rw [heq]
    exact measurableSet_iInter_countable fun q ↦ hf (Real.toNNReal q.1 : ℝ≥0∞)

namespace SimpleFunc

theorem measurable (f : SimpleFunc) : Measurable f := by
  intro a
  simpa using f.measurableSet_preimage (Ici a)

theorem measurableSet_le (g : SimpleFunc) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    MeasurableSet {x | g x ≤ f x} :=
  g.measurableSet_cut (fun x a ↦ a ≤ f x) hf

/-- A sequence enumerating the nonnegative rational numbers in `ℝ≥0∞`. -/
def ennrealRatEmbed (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Encodable.decode (α := ℚ) n).getD (0 : ℚ))

theorem ennrealRatEmbed_encode (q : ℚ) :
    ennrealRatEmbed (Encodable.encode q) = Real.toNNReal q := by
  rw [ennrealRatEmbed, Encodable.encodek]
  rfl

/-- Rational-valued simple approximations of a measurable function. -/
def eapprox (f : ℝ → ℝ≥0∞) (n : ℕ) : SimpleFunc :=
  (Finset.range n).sup fun k ↦
    restrict (const (ennrealRatEmbed k)) {x : ℝ | ennrealRatEmbed k ≤ f x}

theorem eapprox_apply {f : ℝ → ℝ≥0∞} {n : ℕ} (x : ℝ) (hf : Measurable f) :
    eapprox f n x =
      (Finset.range n).sup fun k ↦
        if ennrealRatEmbed k ≤ f x then ennrealRatEmbed k else 0 := by
  rw [eapprox]
  rw [finset_sup_apply]
  congr with k
  rw [restrict_apply]
  · simp [indicator_apply]
  · exact hf _

@[gcongr, mono]
theorem monotone_eapprox (f : ℝ → ℝ≥0∞) : Monotone (eapprox f) := by
  intro i j hij
  apply Finset.sup_le
  intro k hk
  simp only [Finset.mem_range] at hk
  apply Finset.le_sup_of_le (b := k)
  · exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le hk hij)
  · exact le_rfl

theorem iSup_eapprox_apply {f : ℝ → ℝ≥0∞} (hf : Measurable f) (x : ℝ) :
    ⨆ n, eapprox f n x = f x := by
  refine le_antisymm (iSup_le fun n ↦ ?_) ?_
  · rw [eapprox_apply x hf]
    refine Finset.sup_le fun k _ ↦ ?_
    split_ifs with hki
    · exact hki
    · exact bot_le
  · refine le_of_not_gt ?_
    intro h
    rcases ENNReal.lt_iff_exists_rat_btwn.1 h with ⟨q, _, hlt_q, hq_lt⟩
    have hq :
        (Real.toNNReal q : ℝ≥0∞) ≤ ⨆ n, eapprox f n x := by
      refine le_iSup_of_le (Encodable.encode q + 1) ?_
      rw [eapprox_apply x hf]
      have hk_mem : Encodable.encode q ∈ Finset.range (Encodable.encode q + 1) :=
        Finset.mem_range.2 (Nat.lt_succ_self _)
      refine le_trans ?_ (Finset.le_sup hk_mem)
      rw [if_pos]
      · rw [ennrealRatEmbed_encode q]
      · simpa [ennrealRatEmbed_encode q] using le_of_lt hq_lt
    exact lt_irrefl _ (lt_of_le_of_lt hq hlt_q)

end SimpleFunc

theorem Measurable.iSup {ι : Type*} [Countable ι] {f : ι → ℝ → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x ↦ ⨆ i, f i x := by
  refine Measurable.of_Ioi fun a ↦ ?_
  have heq : {x | a < ⨆ i, f i x} = ⋃ i, {x | a < f i x} := by
    ext x
    simp [lt_iSup_iff]
  rw [heq]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [MeasurableSet.empty]
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iUnion_congr_of_surjective e he fun _ ↦ rfl]
    exact MeasurableSet.iUnion _ fun n ↦ measurableSet_lt (hf (e n)) a

theorem Measurable.iInf {ι : Type*} [Countable ι] {f : ι → ℝ → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x ↦ ⨅ i, f i x := by
  intro a
  have heq : {x | a ≤ ⨅ i, f i x} = ⋂ i, {x | a ≤ f i x} := by
    ext x
    simp [le_iInf_iff]
  rw [heq]
  exact measurableSet_iInter_countable fun i ↦ hf i a

theorem Measurable.biSup {ι : Type*} (s : Set ι) {f : ι → ℝ → ℝ≥0∞} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun x ↦ ⨆ i ∈ s, f i x := by
  let g : s → ℝ → ℝ≥0∞ := fun i ↦ f i
  have hg : ∀ i : s, Measurable (g i) := fun i ↦ hf i i.2
  letI : Countable s := hs.to_subtype
  simpa [g, iSup_subtype] using (Measurable.iSup (ι := s) hg)

theorem Measurable.biInf {ι : Type*} (s : Set ι) {f : ι → ℝ → ℝ≥0∞} (hs : s.Countable)
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable fun x ↦ ⨅ i ∈ s, f i x := by
  let g : s → ℝ → ℝ≥0∞ := fun i ↦ f i
  have hg : ∀ i : s, Measurable (g i) := fun i ↦ hf i i.2
  letI : Countable s := hs.to_subtype
  simpa [g, iInf_subtype] using (Measurable.iInf (ι := s) hg)

theorem Measurable.add {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x ↦ f x + g x := by
  have heq :
      (fun x ↦ f x + g x) =
        fun x ↦ ⨆ n, (eapprox f n + eapprox g n : SimpleFunc) x := by
    funext x
    calc
      f x + g x = (⨆ n, eapprox f n x) + ⨆ n, eapprox g n x := by
        simp [iSup_eapprox_apply hf x, iSup_eapprox_apply hg x]
      _ = ⨆ n, (eapprox f n + eapprox g n : SimpleFunc) x := by
        rw [ENNReal.iSup_add_iSup_of_monotone]
        · simp
        · intro i j hij
          exact monotone_eapprox _ hij x
        · intro i j hij
          exact monotone_eapprox _ hij x
  rw [heq]
  exact Measurable.iSup fun n ↦ (eapprox f n + eapprox g n).measurable

theorem measurableSet_lt_fun {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | f x < g x} := by
  let S : Type := {q : ℚ // 0 ≤ q}
  have heq :
      {x | f x < g x} =
        ⋃ q : S, {x | f x < (Real.toNNReal q.1 : ℝ≥0∞)} ∩
          {x | (Real.toNNReal q.1 : ℝ≥0∞) ≤ g x} := by
    ext x
    constructor
    · intro hx
      rcases ENNReal.lt_iff_exists_rat_btwn.1 hx with ⟨q, hq0, hfxq, hqg⟩
      refine mem_iUnion.2 ⟨⟨q, hq0⟩, ?_⟩
      simp [hfxq, hqg.le]
    · intro hx
      rcases mem_iUnion.1 hx with ⟨q, hxq⟩
      exact lt_of_lt_of_le
        (by simpa [mem_setOf_eq] using hxq.1)
        (by simpa [mem_setOf_eq] using hxq.2)
  rw [heq]
  exact MeasurableSet.iUnion_countable fun q ↦ by
    have hlt : MeasurableSet {x | f x < (Real.toNNReal q.1 : ℝ≥0∞)} := by
      have heq' : {x | f x < (Real.toNNReal q.1 : ℝ≥0∞)} =
          {x | (Real.toNNReal q.1 : ℝ≥0∞) ≤ f x}ᶜ := by
        ext x
        simp
      rw [heq']
      exact (hf (Real.toNNReal q.1 : ℝ≥0∞)).compl
    exact hlt.inter (hg (Real.toNNReal q.1 : ℝ≥0∞))

theorem Measurable.sub {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x ↦ f x - g x := by
  refine Measurable.of_Ioi fun a ↦ ?_
  have heq : {x | a < f x - g x} = {x | g x + a < f x} := by
    ext x
    simp only [mem_setOf_eq]
    simpa [add_comm] using (lt_tsub_iff_right : a < f x - g x ↔ a + g x < f x)
  rw [heq]
  simpa [add_comm] using measurableSet_lt_fun (hg.add (measurable_const a)) hf

end Real

end MTI
