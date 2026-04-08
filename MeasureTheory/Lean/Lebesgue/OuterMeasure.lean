import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.CompletePartialOrder

set_option autoImplicit false

open Topology ENNReal Set Function

noncomputable section

namespace MTI

namespace Real

def measure (A : Set ℝ) : ℝ≥0∞ :=
  ⨅ (a : ℕ → ℝ) (b : ℕ → ℝ) (_ : A ⊆ ⋃ i, Ioo (a i) (b i)), ∑' i, .ofReal (b i - a i)

theorem measure_le (A : Set ℝ) (a b : ℕ → ℝ)
    (hA : A ⊆ ⋃ i, Ioo (a i) (b i)) :
    measure A ≤ ∑' i, .ofReal (b i - a i) :=
  iInf₂_le_of_le a b (iInf_le_of_le hA (le_of_eq rfl))

@[simp]
theorem measure_empty : measure (∅ : Set ℝ) = 0 := by
  simpa using measure_le ∅ 0 0 (by simp)

theorem measure_Icc_le (a b : ℝ) :
    measure (Icc a b) ≤ .ofReal (b - a) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hab'
  let a' : ℕ → ℝ
    | 0 => a - ε / 2
    | _ + 1 => 0
  let b' : ℕ → ℝ
    | 0 => b + ε / 2
    | _ + 1 => 0
  have ha : a - ε / 2 < a := by
    rw [sub_lt_self_iff]
    exact half_pos hε
  have hb : b < b + ε / 2 := by
    rw [lt_add_iff_pos_right]
    exact half_pos hε
  have :=
    calc
      Icc a b
      _ ⊆ Ioo (a - ε / 2) (b + ε / 2) := Icc_subset_Ioo (by grind) (by grind)
      _ ⊆ ⋃ i, Ioo (a' i) (b' i) := subset_iUnion_of_subset 0 (subset_refl _)
  have := measure_le (Icc a b) a' b' this
  rw [tsum_eq_single 0 ?_] at this
  · calc
      measure (Icc a b)
      _ ≤ ENNReal.ofReal (b' 0 - a' 0) := this
      _ = ENNReal.ofReal (b - a + ε) := by grind
      _ ≤ ENNReal.ofReal (b - a) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (b - a) + ε := by simp
  · intro n hn
    have ha'n : a' n = 0 := by
      cases n with
      | zero => grind
      | succ _ => rfl
    have hb'n : b' n = 0 := by
      cases n with
      | zero => grind
      | succ _ => rfl
    simp [ha'n, hb'n]

theorem measure_Icc (a b : ℝ) : measure (Icc a b) = .ofReal (b - a) := by
  apply le_antisymm (measure_Icc_le a b)
  apply le_iInf₂ fun a' b' ↦ le_iInf (fun hab ↦ ?_)
  suffices
    ∀ (s : Finset ℕ) (a b), Icc a b ⊆ (⋃ i ∈ (s : Set ℕ), Ioo (a' i) (b' i)) →
      (.ofReal (b - a) : ℝ≥0∞) ≤ ∑ i ∈ s, .ofReal ((b' i) - (a' i)) by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : ℕ) (_ : i ∈ univ) ↦ isOpen_Ioo) (by simpa using hab) with
      ⟨s, _, hf, hs⟩
    have e :
        ⋃ i ∈ (hf.toFinset : Set ℕ), Ioo (a' i) (b' i) = ⋃ i ∈ s, Ioo (a' i) (b' i) := by
      simp only [Finset.set_biUnion_coe, Finite.mem_toFinset]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_trans ?_ (le_iSup _ hf.toFinset)
    apply this hf.toFinset _ _ (by simpa only [e])
  clear hab b
  refine fun s ↦ Finset.strongInductionOn s fun s IH a b h ↦ ?_
  by_cases hab' : a > b
  · have : b - a ≤ 0 := by grind
    rw [ENNReal.ofReal_of_nonpos this]
    exact zero_le _
  have a_le_b : a ≤ b := le_of_not_gt hab'
  have := h ⟨a_le_b, le_rfl⟩
  simp only [SetLike.mem_coe, mem_iUnion, mem_Ioo, exists_and_left, exists_prop] at this
  rcases this with ⟨i, cb, is, bd⟩
  rw [← Finset.insert_erase is] at h ⊢
  rw [Finset.coe_insert, biUnion_insert] at h
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  grw [← IH _ (Finset.erase_ssubset is) a (a' i), ← ENNReal.ofReal_add_le]
  · gcongr
    rw [sub_add_sub_cancel]
    exact sub_le_sub_right (bd.le) _
  · rintro x ⟨h₁, h₂⟩
    exact (h ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left (mt And.left (not_lt_of_ge h₂))

@[grind →]
theorem measure_mono {A B : Set ℝ} (h : A ⊆ B) :
    measure A ≤ measure B :=
  iInf₂_mono fun _a _b ↦ iInf_const_mono fun hA ↦ h.trans hA

theorem measure_iUnion_le (A : ℕ → Set ℝ) :
    measure (⋃ n, A n) ≤ ∑' n, measure (A n) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε (hb : (∑' (n : ℕ), measure (A n) < ∞))
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' ℕ with ⟨ε', hε', hl⟩
  apply le_trans _ ((ENNReal.add_le_add_iff_left hb.ne_top).mpr hl.le)
  rw [← ENNReal.tsum_add]
  choose a b hab using
    show ∀ i, ∃ a : ℕ → ℝ, ∃ b : ℕ → ℝ, (A i ⊆ ⋃ i, Ioo (a i) (b i)) ∧
        (∑' i, ENNReal.ofReal (b i - a i)) < measure (A i) + ε' i by
      intro i
      have : measure (A i) < measure (A i) + ε' i :=
        ENNReal.lt_add_right (ne_top_of_le_ne_top hb.ne <| ENNReal.le_tsum _)
          (by simpa using (hε' i).ne')
      rcases iInf_lt_iff.mp this with ⟨a, ht⟩
      rcases iInf_lt_iff.mp ht with ⟨b, ht'⟩
      rcases iInf_lt_iff.mp ht' with ⟨hab, h⟩
      exists a, b
  have hab : ∀ (i : ℕ),
      A i ⊆ ⋃ j, Ioo (a i j) (b i j) ∧
        ∑' (j : ℕ), ENNReal.ofReal (b i j - a i j) < measure (A i) + ε' i := hab
  refine le_trans ?_ (ENNReal.tsum_le_tsum fun i ↦ le_of_lt (hab i).2)
  rw [← ENNReal.tsum_prod, ← Nat.pairEquiv.symm.tsum_eq]
  simp only [Nat.pairEquiv_symm_apply]
  apply le_trans
    (measure_le _
      (fun i ↦ a (Nat.unpair i).1 (Nat.unpair i).2)
      (fun i ↦ b (Nat.unpair i).1 (Nat.unpair i).2) _)
  · apply le_of_eq rfl
  refine iUnion_subset (fun i ↦ (hab i).1.trans (iUnion_subset fun j ↦ ?_))
  rw [iUnion_unpair (fun i j ↦ Ioo (a i j) (b i j))]
  exact subset_iUnion₂_of_subset i j (subset_refl _)

theorem measure_Ico_le (a b : ℝ) :
    measure (Ico a b) ≤ .ofReal (b - a) := by
  have : Ico a b ⊆ Icc a b := by grind
  exact (measure_mono this).trans (measure_Icc_le a b)

theorem measure_Ioo_le (a b : ℝ) :
    measure (Ioo a b) ≤ .ofReal (b - a) := by
  have : Ioo a b ⊆ Icc a b := by grind
  exact (measure_mono this).trans (measure_Icc_le a b)

theorem measure_iUnion_le_countable {ι : Type} [Countable ι] (A : ι → Set ℝ) :
    measure (⋃ i, A i) ≤ ∑' i, measure (A i) := by
  apply rel_iSup_tsum _ measure_empty
  intro B
  calc
    measure (⋃ i, B i) = measure (⋃ i, disjointed B i) := by rw [iUnion_disjointed]
    _ ≤ ∑' i, measure (disjointed B i) := measure_iUnion_le (disjointed B)
    _ ≤ ∑' i, measure (B i) := ENNReal.tsum_le_tsum (fun i ↦ measure_mono (disjointed_subset _ _))

theorem measure_biUnion_le {ι : Type} {I : Set ι}
    (hI : I.Countable) (A : ι → Set ℝ) :
    measure (⋃ i ∈ I, A i) ≤ ∑' i : I, measure (A i) := by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion]
  apply measure_iUnion_le_countable

theorem measure_biUnion_finset {ι : Type} (I : Finset ι) (A : ι → Set ℝ) :
    measure (⋃ i ∈ I, A i) ≤ ∑ i ∈ I, measure (A i) :=
  (measure_biUnion_le I.countable_toSet A).trans_eq <| I.tsum_subtype (measure <| A ·)

theorem measure_iUnion_fintype {ι : Type} [Fintype ι] (A : ι → Set ℝ) :
    measure (⋃ i, A i) ≤ ∑ i, measure (A i) := by
  simpa using measure_biUnion_finset Finset.univ A

theorem measure_union_le (A B : Set ℝ) :
    measure (A ∪ B) ≤ measure A + measure B := by
  simpa [union_eq_iUnion] using measure_iUnion_fintype (cond · A B)

end Real

end MTI

end
