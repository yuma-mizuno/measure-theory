import MeasureTheory.Lean.Lebesgue.OuterMeasure

set_option autoImplicit false

open Topology ENNReal Set Function

noncomputable section

namespace MTI

namespace Real

def IsCaratheodory (A : Set ℝ) : Prop :=
  ∀ B : Set ℝ, measure B = measure (B ∩ A) + measure (B \ A)

theorem measure_c_union {A₁ A₂ : Set ℝ} (h : A₁ ∩ A₂ ⊆ ∅) (h₁ : IsCaratheodory A₁) :
    measure (A₁ ∪ A₂) = measure A₁ + measure A₂ := by
  rw [h₁, Set.union_inter_cancel_left, union_diff_cancel_left h]

theorem isCaratheodory_of_le {A : Set ℝ} (h : ∀ B, measure (B ∩ A) + measure (B \ A) ≤ measure B) :
    IsCaratheodory A := by
  intro C
  symm
  apply le_antisymm
  · exact h C
  · simpa using measure_union_le (C ∩ A) (C \ A)

theorem measure_c_iUnion_finite
    {A : ℕ → Set ℝ} (hA : ∀ n, IsCaratheodory (A n)) (hdA : Pairwise (Disjoint on A)) (n : ℕ) :
    measure (⋃ i, ⋃ (_ : i < n), A i) = ∑ i ∈ Finset.range n, measure (A i) := by
  induction n with
  | zero =>
    simp [measure_empty]
  | succ n ih =>
    rw [biUnion_lt_succ, Finset.sum_range_succ, Set.union_comm, ← ih]
    rw [measure_c_union _ (hA n), add_comm]
    intro a
    simpa using fun (h₁ : a ∈ A n) i (hi : i < n) h₂ ↦ (hdA (ne_of_gt hi)).le_bot ⟨h₁, h₂⟩

theorem isCaratheodory_empty : IsCaratheodory (∅ : Set ℝ) := by
  intro B
  simp [measure_empty, zero_add]

theorem IsCaratheodory.union {A B : Set ℝ} (hA : IsCaratheodory A) (hB : IsCaratheodory B) :
    IsCaratheodory (A ∪ B) := by
  intro C
  have eq₁ :=
    calc measure C
      _ = measure (C ∩ A) + measure (C \ A) := by rw [hA C]
      _ = measure (C ∩ A ∩ B) + measure ((C ∩ A) \ B) +
            measure ((C \ A) ∩ B) + measure ((C \ A) \ B) := by
        grind only [add_assoc, hB (C ∩ A), hB (C \ A)]
  have eq₂ :=
    calc measure (C ∩ (A ∪ B)) + measure (C \ (A ∪ B))
      _ = measure (C ∩ (A ∪ B) ∩ A) + measure ((C ∩ (A ∪ B)) \ A) +
          measure (C \ (A ∪ B)) := by
        rw [hA (C ∩ (A ∪ B))]
      _ = measure (C ∩ A ∩ B) + measure ((C ∩ A) \ B) +
            measure ((C ∩ (A ∪ B)) \ A) + measure (C \ (A ∪ B)) := by
        have : C ∩ (A ∪ B) ∩ A = C ∩ A := by grind
        grind only [hB (C ∩ A)]
  rw [eq₁, eq₂]
  have : (C ∩ (A ∪ B)) \ A = C \ A ∩ B := by grind
  have : (C \ A) \ B = C \ (A ∪ B) := by grind
  grind only

theorem measure_inter_union {A₁ A₂ : Set ℝ} (h : A₁ ∩ A₂ ⊆ ∅) (h₁ : IsCaratheodory A₁) (B : Set ℝ) :
    measure (B ∩ (A₁ ∪ A₂)) = measure (B ∩ A₁) + measure (B ∩ A₂) := by
  rw [h₁, Set.inter_assoc, Set.union_inter_cancel_left, inter_diff_assoc, union_diff_cancel_left h]

theorem isCaratheodory_sum {A : ℕ → Set ℝ} (h : ∀ i, IsCaratheodory (A i))
    (hd : Pairwise (Disjoint on A)) {t : Set ℝ} :
    ∀ {n}, (∑ i ∈ Finset.range n, measure (t ∩ A i)) = measure (t ∩ ⋃ i < n, A i)
  | 0 => by simp
  | Nat.succ n => by
    rw [biUnion_lt_succ, Finset.sum_range_succ, Set.union_comm, isCaratheodory_sum h hd,
      measure_inter_union _ (h n), add_comm]
    intro a
    simpa using fun (h₁ : a ∈ A n) i (hi : i < n) h₂ ↦ (hd (ne_of_gt hi)).le_bot ⟨h₁, h₂⟩

theorem IsCaratheodory.compl {A : Set ℝ} : IsCaratheodory A → IsCaratheodory Aᶜ := by
  intro hA C
  calc
    measure C = measure (C ∩ A) + measure (C \ A) := hA C
    _ = measure (C \ Aᶜ) + measure (C ∩ Aᶜ) := by
      rw [show C ∩ A = C \ Aᶜ by grind, show C \ A = C ∩ Aᶜ by grind]
    _ = measure (C ∩ Aᶜ) + measure (C \ Aᶜ) := by rw [add_comm]

theorem isCaratheodory_compl_iff (A : Set ℝ) : IsCaratheodory Aᶜ ↔ IsCaratheodory A :=
  ⟨fun h ↦ by simpa using h.compl, fun h ↦ h.compl⟩

theorem IsCaratheodory.inter {A₁ A₂ : Set ℝ} (h₁ : IsCaratheodory A₁) (h₂ : IsCaratheodory A₂) :
    IsCaratheodory (A₁ ∩ A₂) := by
  rw [← isCaratheodory_compl_iff, Set.compl_inter]
  exact h₁.compl.union h₂.compl

theorem IsCaratheodory.diff {A₁ A₂ : Set ℝ} (h₁ : IsCaratheodory A₁) (h₂ : IsCaratheodory A₂) :
    IsCaratheodory (A₁ \ A₂) :=
  h₁.inter h₂.compl

theorem isCaratheodory_accumulate {A : ℕ → Set ℝ} (h : ∀ i, IsCaratheodory (A i)) (n : ℕ) :
    IsCaratheodory (accumulate A n) := by
  induction n with
  | zero => simpa [accumulate_zero_nat] using h 0
  | succ n ih => simpa [accumulate_succ] using ih.union (h (n + 1))

theorem isCaratheodory_disjointed {A : ℕ → Set ℝ} (h : ∀ i, IsCaratheodory (A i)) (i : ℕ) :
    IsCaratheodory (disjointed A i) :=
  disjointedRec (fun _ j ht ↦ ht.diff <| h j) (h i)

theorem measure_c_iUnion_of_monotone {A : ℕ → Set ℝ}
    (hA : ∀ i, IsCaratheodory (A i)) (hA_mono : Monotone A) :
    measure (⋃ i, A i) = ⨆ i, measure (A i) := by
  refine le_antisymm ?_ (iSup_le fun i ↦ measure_mono <| subset_iUnion _ _)
  calc
    measure (⋃ n, A n) = measure (⋃ n, disjointed A n) := by rw [iUnion_disjointed]
    _ ≤ ∑' n, measure (disjointed A n) := measure_iUnion_le _
    _ = ⨆ n, ∑ i ∈ Finset.range n, measure (disjointed A i) := ENNReal.tsum_eq_iSup_nat
    _ ≤ ⨆ n, measure (A n) := iSup_mono fun n => by
      calc
        ∑ i ∈ Finset.range n, measure (disjointed A i) =
            measure (⋃ i ∈ Finset.range n, disjointed A i) := by
          rw [← measure_c_iUnion_finite (isCaratheodory_disjointed hA) (disjoint_disjointed A)]
          apply le_antisymm <;> apply measure_mono <;> simp
        _ ≤ measure (⋃ i ∈ Finset.range n, A i) :=
          measure_mono (iUnion₂_mono fun n _hn => disjointed_subset _ _)
        _ ≤ measure (A n) := measure_mono <| iUnion₂_subset <| by
          intro i hi
          apply hA_mono
          exact Finset.mem_range_le hi

theorem isCaratheodory_iUnion_of_disjoint {A : ℕ → Set ℝ} (h : ∀ i, IsCaratheodory (A i))
    (hd : Pairwise (Disjoint on A)) : IsCaratheodory (⋃ i, A i) := by
  apply isCaratheodory_of_le
  intro B
  have hp : measure (B ∩ ⋃ i, A i) ≤ ⨆ n, measure (B ∩ ⋃ i < n, A i) := by
    convert measure_iUnion_le fun i ↦ B ∩ A i using 1
    · simp [inter_iUnion]
    · simp only [ENNReal.tsum_eq_iSup_nat]
      apply iSup_congr (fun n ↦ (isCaratheodory_sum h hd).symm)
  grw [hp]
  rw [ENNReal.iSup_add]
  refine iSup_le fun n ↦ ?_
  calc
    measure (B ∩ ⋃ i, ⋃ (_ : i < n), A i) + measure (B \ ⋃ i, A i)
    _ ≤ measure (B ∩ ⋃ i, ⋃ (_ : i < n), A i) + measure (B \ ⋃ i, ⋃ (_ : i < n), A i) := by
      gcongr
      refine measure_mono (diff_subset_diff_right ?_)
      exact iUnion₂_subset fun i _ ↦ subset_iUnion _ i
    _ = measure B := by
      have h : IsCaratheodory (⋃ i, ⋃ (_ : i < n), A i) := by
        induction n with
        | zero => simpa using isCaratheodory_empty
        | succ n ih =>
          rw [biUnion_lt_succ]
          apply ih.union (h n)
      apply (h B).symm

theorem isCaratheodory_iUnion {A : ℕ → Set ℝ} (h : ∀ i, IsCaratheodory (A i)) :
    IsCaratheodory (⋃ i, A i) := by
  rw [← iUnion_disjointed]
  exact isCaratheodory_iUnion_of_disjoint (isCaratheodory_disjointed h) (disjoint_disjointed _)

theorem measure_c_accumulate
    {A : ℕ → Set ℝ} (hA : ∀ n, IsCaratheodory (A n)) (hdA : Pairwise (Disjoint on A)) (n : ℕ) :
    measure (accumulate A n) = ∑ i ∈ Finset.range (n + 1), measure (A i) := by
  simp only [accumulate_def, Nat.le_iff_lt_add_one]
  apply measure_c_iUnion_finite hA hdA

theorem measure_c_iUnion (A : ℕ → Set ℝ)
    (hA : ∀ n, IsCaratheodory (A n)) (hdA : Pairwise (Disjoint on A)) :
    measure (⋃ n, A n) = ∑' n, measure (A n) :=
  calc
    measure (⋃ n, A n) = measure (⋃ n, accumulate A n) := by
      rw [iUnion_accumulate]
    _ = ⨆ n, measure (accumulate A n) :=
      measure_c_iUnion_of_monotone (isCaratheodory_accumulate hA) monotone_accumulate
    _ = ⨆ n, ∑ i ∈ Finset.range (n + 1), measure (A i) :=
      iSup_congr (measure_c_accumulate hA hdA)
    _ = ∑' n, measure (A n) :=
      (ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)).symm

end Real

end MTI

end
