import Mathlib.Order.Interval.Set.Infinite
import MeasureTheory.Lean.Lebesgue.MeasurableCaratheodory

noncomputable section

set_option autoImplicit false

open ENNReal Set Function

namespace MTI

namespace Real

def rationalRel (x y : ℝ) : Prop := ∃ q : ℚ, x - y = (q : ℝ)

theorem rationalRel_refl (x : ℝ) : rationalRel x x := ⟨0, by simp⟩

theorem rationalRel_symm {x y : ℝ} (h : rationalRel x y) : rationalRel y x := by
  rcases h with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hq

theorem rationalRel_trans {x y z : ℝ} (hxy : rationalRel x y) (hyz : rationalRel y z) :
    rationalRel x z := by
  rcases hxy with ⟨q1, hq1⟩
  rcases hyz with ⟨q2, hq2⟩
  refine ⟨q1 + q2, ?_⟩
  change x - z = ((q1 + q2 : ℚ) : ℝ)
  calc
    x - z = (x - y) + (y - z) := by ring
    _ = (q1 : ℝ) + (q2 : ℝ) := by rw [hq1, hq2]
    _ = ((q1 + q2 : ℚ) : ℝ) := by simp

def vitaliSetoid : Setoid (Icc 0 1 : Set ℝ) where
  r x y := rationalRel x y
  iseqv := ⟨fun x ↦ rationalRel_refl x, rationalRel_symm, rationalRel_trans⟩

local instance : Setoid (Icc 0 1 : Set ℝ) := vitaliSetoid

def vitaliSet : Set ℝ :=
  Set.range fun q : Quotient vitaliSetoid ↦ (Quotient.out q : (Icc 0 1 : Set ℝ))

theorem vitaliSet_subset_Icc_zero_one : vitaliSet ⊆ Icc 0 1 := by
  rintro x ⟨q, rfl⟩
  exact (Quotient.out q).2

theorem existsUnique_mem_vitaliSet_rationalRel (x : ↥(Icc 0 1 : Set ℝ)) :
    ∃! y : (Icc 0 1 : Set ℝ), (y : ℝ) ∈ vitaliSet ∧ rationalRel x y := by
  let qx : Quotient vitaliSetoid := Quotient.mk'' x
  refine ⟨Quotient.out qx, ⟨⟨qx, rfl⟩, rationalRel_symm (Quotient.mk_out' x)⟩, ?_⟩
  intro y hy
  rcases hy.1 with ⟨q, hq⟩
  have hqy : Quotient.out q = y := Subtype.ext hq
  have hqqx :=
    calc
      q = Quotient.mk'' (Quotient.out q) := (Quotient.out_eq' q).symm
      _ = Quotient.mk'' y := by rw [hqy]
      _ = qx := by
        simpa [qx] using (Quotient.sound hy.2).symm
  simpa [hqy] using congrArg Quotient.out hqqx

@[simp]
theorem measure_Icc_zero_one : measure (Icc 0 1) = 1 := by
  simpa using measure_Icc 0 1

def translate (A : Set ℝ) (c : ℝ) : Set ℝ := {x | x - c ∈ A}

@[simp]
theorem mem_translate {A : Set ℝ} {c x : ℝ} : x ∈ translate A c ↔ x - c ∈ A := Iff.rfl

@[simp]
theorem translate_zero (A : Set ℝ) : translate A 0 = A := by grind [translate]

@[simp]
theorem translate_empty (c : ℝ) : translate (∅ : Set ℝ) c = ∅ := by grind [translate]

@[simp]
theorem translate_Ici (a c : ℝ) : translate (Ici a) c = Ici (a + c) := by
  ext x
  grind [translate]

@[simp] theorem translate_iUnion {ι : Type*} (A : ι → Set ℝ) (c : ℝ) :
    translate (⋃ n, A n) c = ⋃ n, translate (A n) c := by
  ext x
  simp [translate]

@[simp] theorem translate_compl (A : Set ℝ) (c : ℝ) : translate Aᶜ c = (translate A c)ᶜ := by
  ext x
  simp [translate]

@[simp] theorem translate_translate (A : Set ℝ) (c d : ℝ) :
    translate (translate A c) d = translate A (c + d) := by
  ext x
  grind [translate]

theorem MeasurableSet.translate {A : Set ℝ} (hA : MeasurableSet A) (c : ℝ) :
    MeasurableSet (translate A c) := by
  induction hA with
  | ici' a => simpa using MeasurableSet.ici (a + c)
  | empty' => simp
  | compl' A _ ih => simpa using ih.compl
  | iUnion' A hA ih => simpa [translate_iUnion] using MeasurableSet.iUnion _ ih

theorem measure_translate_le (A : Set ℝ) (c : ℝ) : measure (translate A c) ≤ measure A := by
  refine le_iInf fun a => le_iInf fun b => le_iInf fun hA => ?_
  have hA' : translate A c ⊆ ⋃ n, Ioo (a n + c) (b n + c) := by
    intro x hx
    rcases mem_iUnion.1 (hA hx) with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, ?_⟩
    rcases hn with ⟨hna, hnb⟩
    constructor <;> grind
  calc
    measure (translate A c)
      ≤ ∑' n, ENNReal.ofReal ((b n + c) - (a n + c)) := measure_le _ _ _ hA'
    _ = ∑' n, ENNReal.ofReal (b n - a n) := by simp

theorem measure_translate (A : Set ℝ) (c : ℝ) : measure (translate A c) = measure A := by
  refine le_antisymm (measure_translate_le A c) ?_
  simpa [translate_translate, translate_zero] using
    (measure_translate_le (translate A c) (-c))

theorem Icc_zero_one_subset_iUnion_translate_vitaliSet :
    Icc 0 1 ⊆ ⋃ q : (Icc (-1) 1 : Set ℚ), translate vitaliSet (q : ℚ) := by
  intro x hx
  rcases existsUnique_mem_vitaliSet_rationalRel ⟨x, hx⟩ with ⟨y, hy, _hyuniq⟩
  rcases hy.2 with ⟨q, hq⟩
  have hq_lower : (-1 : ℚ) ≤ q := by
    exact_mod_cast (by grind [hx.1, y.2.2] : (-1 : ℝ) ≤ (q : ℝ))
  have hq_upper : q ≤ (1 : ℚ) := by
    exact_mod_cast (by grind [hx.2, y.2.1] : (q : ℝ) ≤ 1)
  let q' : (Icc (-1) 1 : Set ℚ) := ⟨q, ⟨hq_lower, hq_upper⟩⟩
  refine mem_iUnion.2 ⟨q', ?_⟩
  have hxq : x - (q : ℝ) = (y : ℝ) := by grind
  simpa [translate, q', hxq] using hy.1

theorem measure_vitaliSet_ne_zero : measure vitaliSet ≠ 0 := by
  by_contra hzero
  suffices hcontra : (1 : ℝ≥0∞) ≤ 0 by simp at hcontra
  calc
    (1 : ℝ≥0∞) = measure (Icc 0 1) := measure_Icc_zero_one.symm
    _ ≤ measure (⋃ q : (Icc (-1) 1 : Set ℚ), translate vitaliSet (q : ℚ)) := by
      exact measure_mono Icc_zero_one_subset_iUnion_translate_vitaliSet
    _ ≤ ∑' q : (Icc (-1) 1 : Set ℚ), measure (translate vitaliSet (q : ℚ)) :=
      measure_iUnion_le_countable _
    _ = 0 := by simp [measure_translate, hzero]

theorem translate_subset_Icc_zero_two {E : Set ℝ} (hE : E ⊆ Icc 0 1) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : translate E c ⊆ Icc 0 2 := by
  intro x hx
  grind [(hE hx).1, (hE hx).2]

theorem disjoint_translate_of_subset_vitaliSet {E : Set ℝ} (hE : E ⊆ vitaliSet)
    {q r : ℚ} (hqr : q ≠ r) :
    Disjoint (translate E q) (translate E r) := by
  rw [Set.disjoint_left]
  intro x hxq hxr
  let y : (Icc 0 1 : Set ℝ) := ⟨x - q, vitaliSet_subset_Icc_zero_one (hE hxq)⟩
  let z : (Icc 0 1 : Set ℝ) := ⟨x - r, vitaliSet_subset_Icc_zero_one (hE hxr)⟩
  have hyz : (y : ℝ) = (z : ℝ) := congrArg Subtype.val <|
      (existsUnique_mem_vitaliSet_rationalRel y).unique
        ⟨hE hxq, rationalRel_refl _⟩ <| by
    refine ⟨hE hxr, ⟨r - q, ?_⟩⟩
    calc
      (x - q) - (x - r) = r - q := by ring
      _ = ((r - q : ℚ) : ℝ) := by simp
  have hxy : x - q = x - r := by simpa [y, z] using hyz
  exact hqr (Rat.cast_inj.mp (by grind : (q : ℝ) = r))

theorem measure_eq_zero_of_measurableSet_subset_vitaliSet {E : Set ℝ}
    (hE : MeasurableSet E) (hEV : E ⊆ vitaliSet) : measure E = 0 := by
  by_contra hE0
  let ι : Set ℚ := Ioc 0 1
  haveI : Infinite ι := by
    simpa [ι] using (Set.Ioc.infinite (by norm_num : (0 : ℚ) < 1))
  let A : ι → Set ℝ := fun q ↦ translate E (q : ℚ)
  have hAdisj : Pairwise (Disjoint on A) := by
    intro q r hqr
    exact disjoint_translate_of_subset_vitaliSet hEV fun h ↦ hqr (Subtype.ext h)
  have hAsub : ⋃ n, A n ⊆ Icc 0 2 := by
    intro x hx
    rcases mem_iUnion.1 hx with ⟨q, hq⟩
    exact translate_subset_Icc_zero_two
      (hEV.trans vitaliSet_subset_Icc_zero_one) (q : ℝ)
      (by exact_mod_cast le_of_lt q.2.1) (by exact_mod_cast q.2.2) (by simpa [A] using hq)
  suffices hcontra : (∞ : ℝ≥0∞) ≤ 2 by simp at hcontra
  calc
    ∞ = ∑' _ : ι, measure E := (ENNReal.tsum_const_eq_top_of_ne_zero hE0).symm
    _ = ∑' q : ι, measure (A q) := by
      congr with q
      simpa [A] using (measure_translate E (q : ℚ)).symm
    _ = measure (⋃ q, A q) := (measure_iUnion_countable hAdisj (fun q ↦ hE.translate _)).symm
    _ ≤ measure (Icc 0 2) := measure_mono hAsub
    _ = 2 := by simpa using measure_Icc 0 2

theorem not_measurableSet_vitaliSet : ¬ MeasurableSet vitaliSet :=
  fun h ↦
    measure_vitaliSet_ne_zero <| measure_eq_zero_of_measurableSet_subset_vitaliSet h subset_rfl

theorem exists_not_measurableSet : ∃ A : Set ℝ, ¬ MeasurableSet A :=
  ⟨vitaliSet, not_measurableSet_vitaliSet⟩

theorem measure_compl_vitaliSet_eq_one : measure (Icc 0 1 \ vitaliSet) = 1 := by
  refine le_antisymm ?_ ?_
  · calc
      measure (Icc 0 1 \ vitaliSet) ≤ measure (Icc 0 1) := measure_mono diff_subset
      _ = 1 := measure_Icc_zero_one
  by_contra hlt
  suffices hcontra : measure (Icc 0 1 \ vitaliSet) = 1 from (ne_of_lt (lt_of_not_ge hlt)) hcontra
  rcases exists_measurable_superset_measure_eq (Icc 0 1 \ vitaliSet) with
    ⟨E', hBE', hE'meas, hE'eq⟩
  let F : Set ℝ := E' ∩ Icc 0 1
  have hBsubF : Icc 0 1 \ vitaliSet ⊆ F := fun x hx => ⟨hBE' hx, hx.1⟩
  have hFeq : measure F = measure (Icc 0 1 \ vitaliSet) := by
    refine le_antisymm ?_ (measure_mono hBsubF)
    calc
      measure F ≤ measure E' := measure_mono Set.inter_subset_left
      _ = measure (Icc 0 1 \ vitaliSet) := hE'eq
  let E : Set ℝ := Icc 0 1 \ F
  have hEmeas : MeasurableSet E :=
    (measurableSet_Icc 0 1).diff (hE'meas.inter (measurableSet_Icc 0 1))
  have hEsubV : E ⊆ vitaliSet := by grind
  have hdisj : Disjoint E F := by grind
  calc
    measure (Icc 0 1 \ vitaliSet) = measure F := hFeq.symm
    _ = measure E + measure F := by
      simp [measure_eq_zero_of_measurableSet_subset_vitaliSet hEmeas hEsubV]
    _ = measure (E ∪ F) := by
      rw [← measure_union (Set.disjoint_iff_inter_eq_empty.1 hdisj) hEmeas]
    _ = measure (Icc 0 1) := by
      congr 1
      grind
    _ = 1 := measure_Icc_zero_one

theorem vitaliSet_compl_nonadditive :
    measure (Icc 0 1) ≠ measure vitaliSet + measure (Icc 0 1 \ vitaliSet) := by
  apply ne_of_lt
  calc
    measure (Icc 0 1) = 1 := measure_Icc_zero_one
    _ < measure vitaliSet + 1 := by
      simpa [add_comm] using ENNReal.lt_add_right (by simp) measure_vitaliSet_ne_zero
    _ = measure vitaliSet + measure (Icc 0 1 \ vitaliSet) := by
      rw [measure_compl_vitaliSet_eq_one]

theorem exists_disjoint_nonadditive :
    ∃ A B : Set ℝ, Disjoint A B ∧ measure (A ∪ B) ≠ measure A + measure B := by
  refine ⟨vitaliSet, Icc 0 1 \ vitaliSet, Set.disjoint_sdiff_right, ?_⟩
  simpa [Set.union_diff_cancel vitaliSet_subset_Icc_zero_one] using vitaliSet_compl_nonadditive

end Real

end MTI

end
