import Mathlib.Analysis.SpecificLimits.Basic
import MeasureTheory.Lean.MeasurableSpace

set_option autoImplicit false

open ENNReal Function Set
open Lean PrettyPrinter

noncomputable section
namespace MTI

variable {X : Type*} [MeasurableSpace X]

structure Measure (X : Type*) [MeasurableSpace X] where
  toFun : (A : Set X) → MeasurableSet A → ℝ≥0∞
  empty' : toFun ∅ .empty = 0
  union' : ∀ {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (_hAB : Disjoint A B),
    toFun (A ∪ B) (hA.union hB) = toFun A hA + toFun B hB
  iUnion_of_monotone' : ∀ {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) (_hmono : Monotone A),
    toFun (⋃ i, A i) (.iUnion hA) = ⨆ i, toFun (A i) (hA i)

theorem MeasurableSet.accumulate {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    MeasurableSet (accumulate A n) :=
  MeasurableSet.iUnion (fun k ↦ MeasurableSet.iUnion (fun _ ↦ hA k))

lemma Measure.accumulate_eq_sum' (μ : Measure X)
    {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A)) (n : ℕ) :
    μ.toFun (accumulate A n) (.accumulate hA n) =
      ∑ i ∈ Finset.range (n + 1), μ.toFun (A i) (hA i) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ, ← hn]
    simp only [accumulate_succ]
    rw [μ.union' _ (hA (n + 1))]
    exact Set.disjoint_accumulate hAd (Nat.lt_succ_self n)

theorem Measure.iUnion_of_disjoint' (μ : Measure X) {A : ℕ → Set X}
    (hd : Pairwise (Disjoint on A)) (hA : ∀ n, MeasurableSet (A n)) :
    μ.toFun (⋃ n, A n) (.iUnion hA) = ∑' n, μ.toFun (A n) (hA n) :=
  calc
    μ.toFun (⋃ n, A n) (.iUnion hA)
    _ = μ.toFun (⋃ n, accumulate A n) (.iUnion (.accumulate hA)) := by
      simp [iUnion_accumulate]
    _ = ⨆ n, μ.toFun (accumulate A n) (.accumulate hA n) :=
      μ.iUnion_of_monotone' (.accumulate hA) monotone_accumulate
    _ = ⨆ n, ∑ j ∈ Finset.range (n + 1), μ.toFun (A j) (hA j) :=
      iSup_congr <| Measure.accumulate_eq_sum' μ hA hd
    _ = ∑' n, μ.toFun (A n) (hA n) :=
      (ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)).symm

theorem Measure.iUnion_of_disjoint_countable
    (m : (A : Set X) → MeasurableSet A → ℝ≥0∞)
    (m_empty : m ∅ .empty = 0)
    (m_iUnion : ∀ {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i))
      (_hAd : Pairwise (Disjoint on A)), m (⋃ i, A i) (.iUnion hA) = ∑' i, m (A i) (hA i))
    {ι : Type*} [Countable ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A)) :
    m (⋃ i, A i) (.iUnion hA) = ∑' i, m (A i) (hA i) := by
  classical
  cases nonempty_encodable ι
  let m' : Set X → ℝ≥0∞ := fun s => if hs : MeasurableSet s then m s hs else 0
  have hm' : ∀ {s : Set X} (hs : MeasurableSet s), m' s = m s hs := by
    intro s hs
    simp [m', hs]
  have hm'_empty : m' ∅ = 0 := by simp [m', m_empty]
  have hdecode : ∀ n, MeasurableSet (⋃ i ∈ Encodable.decode₂ ι n, A i) := by
    intro n
    apply Encodable.iUnion_decode₂_cases
    · exact .empty
    · intro i
      exact hA i
  calc
    m (⋃ i, A i) (.iUnion hA)
      = m (⋃ n, ⋃ i ∈ Encodable.decode₂ ι n, A i) (.iUnion hdecode) := by
          congr
          exact (Encodable.iUnion_decode₂ A).symm
    _ = ∑' n, m (⋃ i ∈ Encodable.decode₂ ι n, A i) (hdecode n) :=
      m_iUnion hdecode (Encodable.iUnion_decode₂_disjoint_on hAd)
    _ = ∑' n, m' (⋃ i ∈ Encodable.decode₂ ι n, A i) := by
      refine tsum_congr ?_
      intro n
      symm
      exact hm' (hdecode n)
    _ = ∑' i, m' (A i) := by
      exact tsum_iUnion_decode₂ (β := ι) m' hm'_empty A
    _ = ∑' i, m (A i) (hA i) := by
      refine tsum_congr ?_
      intro i
      exact hm' (hA i)

theorem Measure.union_of_countablyAdditive
    (m : (A : Set X) → MeasurableSet A → ℝ≥0∞)
    (m_empty : m ∅ .empty = 0)
    (m_iUnion : ∀ {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i))
      (_hAd : Pairwise (Disjoint on A)), m (⋃ i, A i) (.iUnion hA) = ∑' i, m (A i) (hA i))
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    m (A ∪ B) (hA.union hB) = m A hA + m B hB := by
  let C : Bool → Set X := fun b ↦ cond b A B
  have hC : ∀ b, MeasurableSet (C b) := fun b ↦ MeasurableSet.cond hA hB
  have hCd : Pairwise (Disjoint on C) := (pairwise_on_bool fun ⦃x y⦄ h ↦ h.symm).mpr hAB
  simpa [union_eq_iUnion, C, tsum_fintype] using
    (iUnion_of_disjoint_countable m m_empty m_iUnion hC hCd)

lemma Measure.accumulate_eq_sum_of_countablyAdditive
    (m : (A : Set X) → MeasurableSet A → ℝ≥0∞)
    (m_empty : m ∅ .empty = 0)
    (m_iUnion : ∀ {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i))
      (_hAd : Pairwise (Disjoint on A)), m (⋃ i, A i) (.iUnion hA) = ∑' i, m (A i) (hA i))
    {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) (n : ℕ) :
    m (accumulate A n) (MeasurableSet.accumulate hA n) =
      ∑ i ∈ Finset.range (n + 1), m (A i) (hA i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        m (accumulate A (n + 1)) (MeasurableSet.accumulate hA (n + 1))
            = m (accumulate A n) (MeasurableSet.accumulate hA n) + m (A (n + 1)) (hA (n + 1)) := by
                simpa [Set.accumulate_succ] using
                  (union_of_countablyAdditive m m_empty m_iUnion
                    (MeasurableSet.accumulate hA n) (hA (n + 1))
                    (Set.disjoint_accumulate hAd (Nat.lt_succ_self n)))
        _ = ∑ i ∈ Finset.range (n + 1), m (A i) (hA i) + m (A (n + 1)) (hA (n + 1)) := by
              rw [ih]
        _ = ∑ i ∈ Finset.range (n + 2), m (A i) (hA i) := by
              exact (Finset.sum_range_succ (f := fun i => m (A i) (hA i)) (n := n + 1)).symm

theorem Measure.iUnion_of_monotone_of_countablyAdditive
    (m : (A : Set X) → MeasurableSet A → ℝ≥0∞)
    (m_empty : m ∅ .empty = 0)
    (m_iUnion : ∀ {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i))
      (_hAd : Pairwise (Disjoint on A)), m (⋃ i, A i) (.iUnion hA) = ∑' i, m (A i) (hA i))
    {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) (hmono : Monotone A) :
    m (⋃ i, A i) (.iUnion hA) = ⨆ i, m (A i) (hA i) := by
  let D : ℕ → Set X := disjointed A
  have hD : ∀ i, MeasurableSet (D i) := by
    intro i
    dsimp only [D]
    simpa [D] using disjointedRec (fun _ j ht => MeasurableSet.diff ht <| hA j) (hA i)
  calc
    m (⋃ i, A i) (.iUnion hA) = m (⋃ i, D i) (.iUnion hD) := by
      simp [D, iUnion_disjointed]
    _ = ∑' i, m (D i) (hD i) := m_iUnion hD (disjoint_disjointed A)
    _ = ⨆ n, ∑ i ∈ Finset.range (n + 1), m (D i) (hD i) := by
      exact ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)
    _ = ⨆ n, m (accumulate D n) (MeasurableSet.accumulate hD n) := by
      refine iSup_congr fun n ↦ ?_
      symm
      exact accumulate_eq_sum_of_countablyAdditive m m_empty m_iUnion hD (disjoint_disjointed A) n
    _ = ⨆ n, m (A n) (hA n) := by
      refine iSup_congr fun n ↦ ?_
      have hacc' : accumulate D n = A n := by
        calc
          accumulate D n = partialSups (disjointed A) n := by
            simpa [D] using congrArg (fun f => f n) (partialSups_eq_accumulate (disjointed A)).symm
          _ = partialSups A n := congrArg (fun f => f n) (partialSups_disjointed A)
          _ = A n := congrArg (fun f => f n) (Monotone.partialSups_eq hmono)
      simp [hacc']

/-- Construct a `Measure` from a countably additive function on measurable sets. Since the current
`Measure` structure also stores continuity from below for monotone sequences, that property is
derived from countable additivity. -/
def Measure.ofCountablyAdditive
    (m : (A : Set X) → MeasurableSet A → ℝ≥0∞)
    (m_empty : m ∅ .empty = 0)
    (m_iUnion : ∀ {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i))
      (_hAd : Pairwise (Disjoint on A)), m (⋃ i, A i) (.iUnion hA) = ∑' i, m (A i) (hA i)) :
    Measure X where
  toFun := m
  empty' := m_empty
  union' := by
    intro A B hA hB hAB
    exact union_of_countablyAdditive m m_empty m_iUnion hA hB hAB
  iUnion_of_monotone' := by
    intro A hA hmono
    exact iUnion_of_monotone_of_countablyAdditive m m_empty m_iUnion hA hmono

def Measure.toOuterMeasure (μ : Measure X) (A : Set X) : ℝ≥0∞ :=
  ⨅ (B : Set X) (_ : A ⊆ B) (hB : MeasurableSet B), μ.toFun B hB

instance : CoeFun (Measure X) (fun _ ↦ Set X → ℝ≥0∞) where
  coe μ := μ.toOuterMeasure

@[app_unexpander MTI.Measure.toOuterMeasure]
meta def unexpandMeasureToOuterMeasure : Unexpander
  | `($_ $μ $A) => `($μ $A)
  | _ => throw ()

theorem Measure.apply_def (μ : Measure X) (A : Set X) :
    μ A = ⨅ (B : Set X) (_ : A ⊆ B) (hB : MeasurableSet B), μ.toFun B hB :=
  rfl

@[simp]
theorem Measure.toFun_apply (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    μ.toFun A hA = μ A := by
  symm
  apply le_antisymm (iInf₂_le_of_le A (subset_refl A) (iInf_le_of_le hA (le_of_eq rfl)))
  apply le_iInf₂ fun B hAB ↦ le_iInf fun hB ↦ ?_
  have hB' : B = A ∪ (B \ A) := by grind
  have hABA : MeasurableSet (A ∪ (B \ A)) := hA.union (hB.diff hA)
  calc μ.toFun A hA ≤ μ.toFun A hA + μ.toFun (B \ A) (hB.diff hA) := le_self_add
    _ = μ.toFun (A ∪ (B \ A)) hABA := (μ.union' _ _ (by grind)).symm
    _ = μ.toFun B hB := by grind

@[simp]
theorem Measure.empty (μ : Measure X) : μ ∅ = 0 := by
  rw [← μ.toFun_apply MeasurableSet.empty]
  apply μ.empty'

@[simp]
theorem Measure.union (μ : Measure X) {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) : μ (A ∪ B) = μ A + μ B := by
  rw [← μ.toFun_apply (hA.union hB), ← μ.toFun_apply hA, ← μ.toFun_apply hB]
  apply μ.union' hA hB hAB

@[simp]
theorem Measure.iUnion_of_monotone (μ : Measure X) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) (hmono : Monotone A) :
    μ (⋃ i, A i) = ⨆ i, μ (A i) := by
  rw [← μ.toFun_apply (MeasurableSet.iUnion hA),
    iSup_congr (fun i ↦ (μ.toFun_apply (hA i)).symm)]
  apply μ.iUnion_of_monotone' hA hmono

theorem Measure.mono (μ : Measure X) {A B : Set X} (h : A ⊆ B) : μ A ≤ μ B := le_iInf
  fun C ↦ le_iInf fun hBC ↦ le_iInf fun hC ↦
    iInf₂_le_of_le C (h.trans hBC) (iInf_le_of_le hC (le_of_eq rfl))

lemma Measure.accumulate_eq_sum (μ : Measure X)
    {A : ℕ → Set X} (hA : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (Disjoint on A)) (n : ℕ) :
    μ (accumulate A n) = ∑ i ∈ Finset.range (n + 1), μ (A i) := by
  simp_rw [← μ.toFun_apply (MeasurableSet.accumulate hA n)]
  simp_rw [← μ.toFun_apply (hA _)]
  apply Measure.accumulate_eq_sum' μ hA hAd n

theorem Measure.iUnion_of_disjoint (μ : Measure X) {A : ℕ → Set X}
    (hd : Pairwise (Disjoint on A)) (hA : ∀ n, MeasurableSet (A n)) :
    μ (⋃ n, A n) = ∑' n, μ (A n) := by
  simp_rw [← μ.toFun_apply (MeasurableSet.iUnion hA)]
  simp_rw [← μ.toFun_apply (hA _)]
  apply Measure.iUnion_of_disjoint' μ hd hA

theorem Measure.iUnion_le_of_measurable (μ : Measure X) {A : ℕ → Set X}
    (hA : ∀ i, MeasurableSet (A i)) :
    μ (⋃ i, A i) ≤ ∑' i, μ (A i) := by
  calc
    μ (⋃ i, A i) = μ (⋃ i, disjointed A i) := by
      rw [iUnion_disjointed]
    _ = ∑' i, μ (disjointed A i) := by
      apply μ.iUnion_of_disjoint (disjoint_disjointed A)
      intro i
      simpa using disjointedRec (fun _ j ht => MeasurableSet.diff ht <| hA j) (hA i)
    _ ≤ ∑' i, μ (A i) := by
      exact ENNReal.tsum_le_tsum (fun i ↦ μ.mono (disjointed_subset A i))

theorem Measure.iUnion_le (μ : Measure X) (A : ℕ → Set X) :
    μ (⋃ i, A i) ≤ ∑' i, μ (A i) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hb
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' ℕ with
    ⟨ε', hε', hεsum⟩
  choose B hAB hB hlt using
    show ∀ i, ∃ B : Set X, ∃ hAB : A i ⊆ B, ∃ hB : MeasurableSet B,
      μ.toFun B hB < μ (A i) + ε' i by
      intro i
      have hlt : μ (A i) < μ (A i) + ε' i := by
        exact ENNReal.lt_add_right (ne_top_of_le_ne_top hb.ne <| ENNReal.le_tsum _)
          (by simpa using (hε' i).ne')
      rw [Measure.apply_def] at hlt
      rcases iInf_lt_iff.mp hlt with ⟨B, hltB⟩
      rcases iInf_lt_iff.mp hltB with ⟨hAB, hltB⟩
      rcases iInf_lt_iff.mp hltB with ⟨hB, hltB⟩
      exact ⟨B, hAB, hB, hltB⟩
  have hsub : (⋃ i, A i) ⊆ ⋃ i, B i := by
    exact iUnion_subset (fun i ↦ (hAB i).trans <| subset_iUnion B i)
  have hlt' : ∀ i, μ (B i) < μ (A i) + ε' i := by
    intro i
    simpa [μ.toFun_apply (hB i)] using hlt i
  calc
    μ (⋃ i, A i) ≤ μ (⋃ i, B i) := μ.mono hsub
    _ ≤ ∑' i, μ (B i) := μ.iUnion_le_of_measurable hB
    _ ≤ ∑' i, (μ (A i) + ε' i) := by
      exact ENNReal.tsum_le_tsum (fun i ↦ (hlt' i).le)
    _ = ∑' i, μ (A i) + ∑' i, (ε' i : ℝ≥0∞) := by
      rw [ENNReal.tsum_add]
    _ ≤ ∑' i, μ (A i) + ε := by
      exact add_le_add le_rfl hεsum.le

theorem Measure.union_le (μ : Measure X) (A B : Set X) :
    μ (A ∪ B) ≤ μ A + μ B := by
  let C : ℕ → Set X
    | 0 => A
    | 1 => B
    | _ => ∅
  calc
    μ (A ∪ B) = μ (⋃ i, C i) := by
      have hCU : (⋃ i, C i) = A ∪ B := by
        ext x
        constructor
        · intro hx
          rcases mem_iUnion.1 hx with ⟨i, hi⟩
          cases i with
          | zero => exact Or.inl (by simpa [C] using hi)
          | succ i =>
              cases i with
              | zero => exact Or.inr (by simpa [C] using hi)
              | succ i =>
                  simp [C] at hi
        · intro hx
          rcases hx with hx | hx
          · exact mem_iUnion.2 ⟨0, by simpa [C] using hx⟩
          · exact mem_iUnion.2 ⟨1, by simpa [C] using hx⟩
      rw [hCU]
    _ ≤ ∑' i, μ (C i) := μ.iUnion_le C
    _ = Finset.sum ({0, 1} : Finset ℕ) (fun i ↦ μ (C i)) := by
      rw [tsum_eq_sum (s := ({0, 1} : Finset ℕ))]
      intro i hi
      have hi0 : i ≠ 0 := by
        intro h
        apply hi
        simp [h]
      have hi1 : i ≠ 1 := by
        intro h
        apply hi
        simp [h]
      cases i with
      | zero => exact (hi0 rfl).elim
      | succ i =>
          cases i with
          | zero => exact (hi1 rfl).elim
          | succ i => simp [C]
    _ = μ A + μ B := by
      simp [C]

theorem Measure.toOuterMeasure_caratheodory (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) (B : Set X) :
    μ B = μ (B ∩ A) + μ (B \ A) := by
  apply le_antisymm
  · calc
      μ B = μ ((B ∩ A) ∪ (B \ A)) := by
        have hBA : ((B ∩ A) ∪ (B \ A)) = B := by
          ext x
          grind
        rw [hBA]
      _ ≤ μ (B ∩ A) + μ (B \ A) := μ.union_le _ _
  · rw [Measure.apply_def]
    apply le_iInf
    intro C
    apply le_iInf
    intro hBC
    apply le_iInf
    intro hC
    calc
      μ (B ∩ A) + μ (B \ A) ≤ μ (C ∩ A) + μ (C \ A) := by
        exact add_le_add
          (μ.mono (by
            intro x hx
            exact ⟨hBC hx.1, hx.2⟩))
          (μ.mono (by
            intro x hx
            exact ⟨hBC hx.1, hx.2⟩))
      _ = μ ((C ∩ A) ∪ (C \ A)) := by
        symm
        apply μ.union (hC.inter hA) (hC.diff hA)
        grind
      _ = μ.toFun C hC := by
        rw [show (C ∩ A) ∪ (C \ A) = C by
          ext x
          grind]
        exact (μ.toFun_apply hC).symm

/-- If a function on all subsets satisfies the three outer-measure axioms and every measurable set
is Carathéodory, then restricting it to measurable sets defines a measure. -/
def Measure.ofOuterMeasure (μ : Set X → ℝ≥0∞)
    (μ_empty : μ ∅ = 0)
    (μ_mono : Monotone μ)
    (μ_iUnion_le : ∀ A : ℕ → Set X, μ (⋃ i, A i) ≤ ∑' i, μ (A i))
    (μ_caratheodory : ∀ {A : Set X}, MeasurableSet A → ∀ B : Set X,
      μ B = μ (B ∩ A) + μ (B \ A)) :
    Measure X := by
  refine Measure.ofCountablyAdditive (fun A _ ↦ μ A) (by simpa using μ_empty) ?_
  intro A hA hAd
  have h_union : ∀ {S T : Set X}, MeasurableSet S → Disjoint S T → μ (S ∪ T) = μ S + μ T := by
    intro S T hS hST
    have hdiff : (S ∪ T) \ S = T := by
      simpa [sup_eq_union] using hST.sup_sdiff_cancel_left
    calc
      μ (S ∪ T) = μ ((S ∪ T) ∩ S) + μ ((S ∪ T) \ S) := μ_caratheodory hS _
      _ = μ S + μ T := by
        rw [hdiff, show (S ∪ T) ∩ S = S by rw [inter_eq_right]; exact subset_union_left]
  apply le_antisymm
  · exact μ_iUnion_le A
  · rw [ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)]
    refine iSup_le fun n ↦ ?_
    have hacc : μ (accumulate A n) = ∑ i ∈ Finset.range (n + 1), μ (A i) := by
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            μ (accumulate A (n + 1))
                = μ (accumulate A n) + μ (A (n + 1)) := by
                    rw [Set.accumulate_succ]
                    exact h_union (MeasurableSet.accumulate hA n)
                      (Set.disjoint_accumulate hAd (Nat.lt_succ_self n))
            _ = ∑ i ∈ Finset.range (n + 1), μ (A i) + μ (A (n + 1)) := by
                  rw [ih]
            _ = ∑ i ∈ Finset.range (n + 2), μ (A i) := by
                  exact (Finset.sum_range_succ (f := fun i ↦ μ (A i)) (n := n + 1)).symm
    calc
      ∑ i ∈ Finset.range (n + 1), μ (A i) = μ (accumulate A n) := hacc.symm
      _ ≤ μ (⋃ i, A i) := μ_mono (Set.accumulate_subset_iUnion n)

end MTI

end
