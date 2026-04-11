import MeasureTheory.Lean.Lebesgue.Caratheodory
import MeasureTheory.Lean.Lebesgue.MeasurableSets

set_option autoImplicit false

open Topology ENNReal Set Function

noncomputable section

namespace MTI

namespace Real

theorem isCaratheodory_Ici (c : ℝ) : IsCaratheodory (Ici c) := by
  apply isCaratheodory_of_le
  intro A
  refine le_iInf fun a ↦ le_iInf fun b ↦ le_iInf fun h ↦ ?_
  calc
    measure (A ∩ Ici c) + measure (A \ Ici c)
    _ ≤ measure (⋃ i, Ioo (a i) (b i) ∩ Ici c) +
        measure (⋃ i, Ioo (a i) (b i) \ Ici c) := by
      refine add_le_add ?_ ?_
      · apply measure_mono
        rw [← iUnion_inter]
        apply inter_subset_inter_left
        exact h
      · apply measure_mono
        rw [← iUnion_diff]
        apply diff_subset_diff_left
        exact h
    _ ≤ ∑' (i : ℕ), measure (Ioo (a i) (b i) ∩ Ici c) +
        ∑' (i : ℕ), measure (Ioo (a i) (b i) \ Ici c) := by
      apply add_le_add
      · exact measure_iUnion_le fun n ↦ Ioo (a n) (b n) ∩ Ici c
      · exact measure_iUnion_le fun n ↦ Ioo (a n) (b n) \ Ici c
    _ = ∑' (i : ℕ), (measure (Ioo (a i) (b i) ∩ Ici c) + measure (Ioo (a i) (b i) \ Ici c)) := by
      exact Eq.symm ENNReal.tsum_add
    _ ≤ ∑' (i : ℕ), .ofReal (b i - a i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rcases lt_or_ge (a i) c with hac | hac <;> rcases lt_or_ge (b i) c with hbc | hbc
      · have : Ioo (a i) (b i) ∩ Ici c = ∅ := by grind
        rw [this]
        have : Ioo (a i) (b i) \ Ici c = Ioo (a i) (b i) := by grind
        rw [this]
        simp only [measure_empty, zero_add, ge_iff_le]
        apply measure_Ioo_le
      · have : Ioo (a i) (b i) ∩ Ici c = Ico c (b i) := by grind
        rw [this]
        have : Ioo (a i) (b i) \ Ici c = Ioo (a i) c := by grind
        rw [this]
        apply le_trans (add_le_add (measure_Ico_le _ _) (measure_Ioo_le _ _))
        apply le_of_eq
        rw [← ENNReal.ofReal_add (by grind) (by grind)]
        simp only [sub_add_sub_cancel]
      · have : Ioo (a i) (b i) = ∅ := by grind
        simp [this]
      · have : Ioo (a i) (b i) ∩ Ici c = Ioo (a i) (b i) := by grind
        rw [this]
        have : Ioo (a i) (b i) \ Ici c = ∅ := by grind
        rw [this]
        simp only [measure_empty, add_zero, ge_iff_le]
        apply measure_Ioo_le

theorem MeasurableSet.isCaratheodory {A : Set ℝ} (h : MeasurableSet A) :
    IsCaratheodory A := by
  induction h with
  | ici' c => apply isCaratheodory_Ici c
  | empty' => apply isCaratheodory_empty
  | compl' A hA ih => apply ih.compl
  | iUnion' A hA ih => apply isCaratheodory_iUnion ih

theorem measure_union {A₁ A₂ : Set ℝ} (h : A₁ ∩ A₂ = ∅) (h₁ : MeasurableSet A₁) :
    measure (A₁ ∪ A₂) = measure (A₁) + measure (A₂) :=
  measure_c_union h (h₁.isCaratheodory)

theorem measure_iUnion (A : ℕ → Set ℝ)
    (hA : ∀ n, MeasurableSet (A n)) (hdA : Pairwise (Disjoint on A)) :
    measure (⋃ n, A n) = ∑' n, measure (A n) :=
  measure_c_iUnion A (fun n ↦ (hA n).isCaratheodory) hdA

theorem measure_m_iUnion_of_monotone {A : ℕ → Set ℝ}
    (hA : ∀ i, MeasurableSet (A i)) (hmA : Monotone A) :
    measure (⋃ i, A i) = ⨆ i, measure (A i) :=
  measure_c_iUnion_of_monotone (fun i ↦ (hA i).isCaratheodory) hmA

theorem measure_iUnion_countable {ι : Type} [Countable ι] {A : ι → Set ℝ}
    (hn : Pairwise (Disjoint on A)) (h : ∀ i, MeasurableSet (A i)) :
    measure (⋃ i, A i) = ∑' i, measure (A i) := by
  cases nonempty_encodable ι
  rw [← Encodable.iUnion_decode₂, ← tsum_iUnion_decode₂ _ measure_empty]
  rw [← measure_iUnion _ _ (Encodable.iUnion_decode₂_disjoint_on hn)]
  intro n
  apply Encodable.iUnion_decode₂_cases
  · exact MeasurableSet.empty
  · intro i
    exact h i

theorem measure_eq_iInf (A : Set ℝ) :
    measure A = ⨅ B, ⨅ (_ : A ⊆ B), ⨅ (_ : MeasurableSet B), measure B := by
  refine le_antisymm (le_iInf fun B ↦ le_iInf fun hAB ↦ le_iInf fun hB ↦ measure_mono hAB) ?_
  refine le_iInf fun a => le_iInf fun b => le_iInf fun hab =>
    ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
  grw [← hε]
  rw [← ENNReal.tsum_add]
  choose B hB using
    show ∀ i, ∃ s, Ioo (a i) (b i) ⊆ s ∧ MeasurableSet s ∧
        measure s ≤ .ofReal (b i - a i) + .ofReal (ε' i) by
      intro i
      have hl :=
        ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_pos.2 (ε'0 i)).ne'
      have habε : Ioo (a i) (b i) ⊆ Ioo (a i) (b i + ε' i) := by
        have : (ε' i : ℝ) > 0 := by simp [ε'0 i]
        grind
      refine ⟨Ioo (a i) (b i + ε' i), habε, measurableSet_Ioo _ _, ?_⟩
      calc measure (Ioo (a i) (b i + ε' i))
      _ ≤ .ofReal ((b i + ε' i) - a i) := by apply measure_Ioo_le
      _ ≤ .ofReal (b i - a i + ε' i) := by grind
      _ ≤ .ofReal (b i - a i) + .ofReal (ε' i) := by
        rw [ofReal_coe_nnreal, coe_nnreal_eq (ε' i)]
        apply ENNReal.ofReal_add_le
  simp only [ofReal_coe_nnreal] at hB
  apply iInf_le_of_le (iUnion B) _
  apply iInf_le_of_le (hab.trans <| iUnion_mono fun i => (hB i).1) _
  apply iInf_le_of_le (MeasurableSet.iUnion _ fun i => (hB i).2.1) _
  exact le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun i => (hB i).2.2)

theorem exists_measurable_superset_measure_eq (A : Set ℝ) :
    ∃ B, A ⊆ B ∧ MeasurableSet B ∧ measure B = measure A := by
  by_cases hA : measure A = ∞
  · refine ⟨Set.univ, Set.subset_univ _, MeasurableSet.univ, ?_⟩
    rw [hA]
    exact le_antisymm le_top (by simpa [hA] using measure_mono (Set.subset_univ A))
  · have hex :
        ∀ r, measure A < r → ∃ B, A ⊆ B ∧ MeasurableSet B ∧ measure B < r := by
      intro r hr
      have hApprox :
          (⨅ B, ⨅ (_ : A ⊆ B), ⨅ (_ : MeasurableSet B), measure B) < r := by
        simpa only [measure_eq_iInf A] using hr
      rcases iInf_lt_iff.mp hApprox with ⟨B, hB⟩
      rcases iInf_lt_iff.mp hB with ⟨hAB, hB⟩
      rcases iInf_lt_iff.mp hB with ⟨hMeas, hB⟩
      exact ⟨B, hAB, hMeas, hB⟩
    have ha : ∃ a : ℕ → ℝ≥0∞, ⨅ i, a i = 0 ∧ ∀ n, a n ≠ 0 := by
      refine ⟨fun n ↦ 1 / (n + 1 : ℝ≥0∞), le_antisymm ?_ (zero_le _), fun n ↦ by simp⟩
      refine ENNReal.le_of_forall_pos_le_add ?_
      intro ε hε h0
      have ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have hε' : (((n : ℝ≥0∞) + 1)⁻¹) ≤ ε := by
        simpa [one_div, Nat.cast_add] using
          (show (((1 / (n + 1 : NNReal)) : NNReal) : ℝ≥0∞) ≤ ε by exact_mod_cast hn.le)
      exact (iInf_le _ n).trans (by simpa using hε')
    rcases ha with ⟨a, ha0, hane⟩
    have hBa : ∀ n : ℕ, ∃ B, A ⊆ B ∧ MeasurableSet B ∧ measure B < measure A + a n :=
      fun n ↦ hex _ (ENNReal.lt_add_right hA (by simpa using hane n))
    choose B hAB hBMeas hBlt using hBa
    refine ⟨⋂ n, B n, Set.subset_iInter hAB, MeasurableSet.iInter hBMeas, le_antisymm ?_ ?_⟩
    · calc
        measure (⋂ n, B n) ≤ ⨅ n, measure (B n) :=
          le_iInf fun n ↦ measure_mono (Set.iInter_subset (fun i ↦ B i) n)
        _ ≤ ⨅ n, (measure A + a n) := iInf_mono fun n ↦ (hBlt n).le
        _ = measure A + ⨅ n, a n := by rw [← ENNReal.add_iInf]
        _ = measure A := by simp [ha0]
    · exact measure_mono (Set.subset_iInter hAB)

theorem measure_iUnion_of_monotone {A : ℕ → Set ℝ} (hA : Monotone A) :
    measure (⋃ i, A i) = ⨆ i, measure (A i) := by
  refine le_antisymm ?_ (iSup_le fun i ↦ measure_mono <| subset_iUnion _ i)
  choose B hAB hBMeas hBeq using fun n ↦ exists_measurable_superset_measure_eq (A n)
  have hAC : ∀ n, A n ⊆ ⋂ i, B (n + i) := by
    intro n x hx
    simp only [mem_iInter]
    intro i
    exact hAB (n + i) ((hA <| Nat.le_add_right n i) hx)
  have hCMeas : ∀ n, MeasurableSet (⋂ i, B (n + i)) := by
    intro n
    exact MeasurableSet.iInter fun i ↦ hBMeas (n + i)
  have hCmono : Monotone (fun n ↦ ⋂ i, B (n + i)) := by
    intro n m hnm x hx
    rcases Nat.exists_eq_add_of_le hnm with ⟨k, rfl⟩
    simp only [mem_iInter] at hx ⊢
    intro i
    simpa [Nat.add_assoc] using hx (k + i)
  have hCeq : ∀ n, measure (⋂ i, B (n + i)) = measure (A n) := by
    intro n
    have hsubset : ⋂ i, B (n + i) ⊆ B n := by
      simpa using (iInter_subset (fun i ↦ B (n + i)) 0)
    refine le_antisymm ?_ (measure_mono (hAC n))
    calc
      measure (⋂ i, B (n + i)) ≤ measure (B n) := measure_mono hsubset
      _ = measure (A n) := hBeq n
  calc
    measure (⋃ i, A i) ≤ measure (⋃ i, ⋂ j, B (i + j)) := measure_mono <| iUnion_mono hAC
    _ = ⨆ i, measure (⋂ j, B (i + j)) := measure_m_iUnion_of_monotone hCMeas hCmono
    _ = ⨆ i, measure (A i) := by
      refine iSup_congr fun n ↦ hCeq n

end Real

end MTI

end
