import Mathlib.Order.Interval.Set.Infinite
import MeasureTheory.Lean.Lebesgue.MeasurableCaratheodory

noncomputable section

set_option autoImplicit false

open ENNReal Set Function

namespace MTI

namespace Real

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

structure IsVitali (A : Set ℝ) : Prop where
  exists_rational : ∀ x : ℝ, ∃! q : ℚ, x - q ∈ A
  subset_Icc_zero_one : A ⊆ Icc 0 1

@[simp]
theorem measure_Icc_zero_one : measure (Icc 0 1) = 1 := by
  simpa using measure_Icc 0 1

theorem IsVitali.pairwise_disjoint_translates {A : Set ℝ} (hA : IsVitali A)
    {q r : ℚ} (hqr : q ≠ r) : translate A q ∩ translate A r = ∅ := by
  ext x
  constructor
  · rintro ⟨hxq, hxr⟩
    rcases hA.exists_rational x with ⟨s, _, hsuniq⟩
    exact (hqr ((hsuniq q hxq).trans (hsuniq r hxr).symm)).elim
  · simp

theorem IsVitali.Icc_zero_one_subset_iUnion_translate {A : Set ℝ} (hA : IsVitali A) :
    Icc 0 1 ⊆ ⋃ q : (Icc (-1) 1 : Set ℚ), translate A (q : ℚ) := by
  intro x hx
  rcases hA.exists_rational x with ⟨q, hqA, _⟩
  have hq_lower : (-1 : ℚ) ≤ q := by
    suffices (q : ℝ) ≥ -1 by exact_mod_cast this
    have hxq : x - (q : ℝ) ∈ Icc 0 1 := hA.subset_Icc_zero_one hqA
    grind [hx.1, hxq.2]
  have hq_upper : q ≤ (1 : ℚ) := by
    suffices (q : ℝ) ≤ 1 by exact_mod_cast this
    have hxq : x - (q : ℝ) ∈ Icc 0 1 := hA.subset_Icc_zero_one hqA
    grind [hx.2, hxq.1]
  refine mem_iUnion.2 ⟨⟨q, ⟨hq_lower, hq_upper⟩⟩, ?_⟩
  simpa [translate] using hqA

theorem IsVitali.measure_ne_zero {A : Set ℝ} (hA : IsVitali A) : measure A ≠ 0 := by
  by_contra hzero
  suffices hcontra : (1 : ℝ≥0∞) ≤ 0 by simp at hcontra
  calc
    (1 : ℝ≥0∞) = measure (Icc 0 1) := measure_Icc_zero_one.symm
    _ ≤ measure (⋃ q : (Icc (-1) 1 : Set ℚ), translate A (q : ℚ)) := by
      exact measure_mono hA.Icc_zero_one_subset_iUnion_translate
    _ ≤ ∑' q : (Icc (-1) 1 : Set ℚ), measure (translate A (q : ℚ)) :=
      measure_iUnion_le_countable _
    _ = 0 := by simp [measure_translate, hzero]

theorem translate_subset_Icc_zero_two {E : Set ℝ} (hE : E ⊆ Icc 0 1) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : translate E c ⊆ Icc 0 2 := by
  intro x hx
  grind [(hE hx).1, (hE hx).2]

theorem IsVitali.disjoint_translate_of_subset {A E : Set ℝ} (hA : IsVitali A) (hE : E ⊆ A)
    {q r : ℚ} (hqr : q ≠ r) :
    translate E q ∩ translate E r = ∅ := by
  ext x
  constructor
  · intro hx
    have hdisj := hA.pairwise_disjoint_translates hqr
    have hxA : x ∈ translate A q ∩ translate A r := ⟨hE hx.1, hE hx.2⟩
    rw [hdisj] at hxA
    exact hxA
  · simp

theorem IsVitali.measure_eq_zero_of_measurableSet_subset {A E : Set ℝ} (hA : IsVitali A)
    (hE : MeasurableSet E) (hEA : E ⊆ A) : measure E = 0 := by
  let ι : Set ℚ := Ioc 0 1
  let B : ι → Set ℝ := fun q ↦ translate E (q : ℚ)
  have hBdisj : Pairwise (Disjoint on B) := by
    intro q r hqr
    suffices B q ∩ B r = ∅ from Set.disjoint_iff_inter_eq_empty.2 this
    exact hA.disjoint_translate_of_subset hEA fun h ↦ hqr (Subtype.ext h)
  have hBsub : ⋃ q, B q ⊆ Icc 0 2 := by
    intro x hx
    rcases mem_iUnion.1 hx with ⟨q, hq⟩
    exact translate_subset_Icc_zero_two
      (hEA.trans hA.subset_Icc_zero_one) (q : ℝ)
      (by exact_mod_cast le_of_lt q.2.1)
      (by exact_mod_cast q.2.2)
      (by simpa [B] using hq)
  by_contra hE0
  suffices hcontra : (∞ : ℝ≥0∞) ≤ 2 by simp at hcontra
  calc
    ∞ = ∑' _ : ι, measure E := (ENNReal.tsum_const_eq_top_of_ne_zero hE0).symm
    _ = ∑' q : ι, measure (B q) := by
      congr with q
      simpa [B] using (measure_translate E (q : ℚ)).symm
    _ = measure (⋃ q, B q) := (measure_iUnion_countable hBdisj (fun q ↦ hE.translate _)).symm
    _ ≤ measure (Icc 0 2) := measure_mono hBsub
    _ = 2 := by simpa using measure_Icc 0 2

theorem IsVitali.not_measurableSet {A : Set ℝ} (hA : IsVitali A) : ¬ MeasurableSet A :=
  fun h ↦ hA.measure_ne_zero <| hA.measure_eq_zero_of_measurableSet_subset h subset_rfl

theorem IsVitali.measure_compl_eq_one {A : Set ℝ} (hA : IsVitali A) :
    measure (Icc 0 1 \ A) = 1 := by
  refine le_antisymm ?_ ?_
  · calc
      measure (Icc 0 1 \ A) ≤ measure (Icc 0 1) := measure_mono diff_subset
      _ = 1 := measure_Icc_zero_one
  by_contra hlt
  suffices hcontra : measure (Icc 0 1 \ A) = 1 from (ne_of_lt (lt_of_not_ge hlt)) hcontra
  rcases exists_measurable_superset_measure_eq (Icc 0 1 \ A) with
    ⟨E', hE', hE'meas, hE'eq⟩
  let F : Set ℝ := E' ∩ Icc 0 1
  have hBsubF : Icc 0 1 \ A ⊆ F := fun x hx => ⟨hE' hx, hx.1⟩
  have hFeq : measure F = measure (Icc 0 1 \ A) := by
    refine le_antisymm ?_ (measure_mono hBsubF)
    calc
      measure F ≤ measure E' := measure_mono Set.inter_subset_left
      _ = measure (Icc 0 1 \ A) := hE'eq
  let E : Set ℝ := Icc 0 1 \ F
  have hEmeas : MeasurableSet E :=
    (measurableSet_Icc 0 1).diff (hE'meas.inter (measurableSet_Icc 0 1))
  have hEsubA : E ⊆ A := by
    intro x hx
    by_contra hxA
    have hxdiff : x ∈ Icc 0 1 \ A := ⟨hx.1, hxA⟩
    have hxF : x ∈ F := ⟨hE' hxdiff, hx.1⟩
    exact hx.2 hxF
  have hEF : E ∩ F = ∅ := Set.disjoint_iff_inter_eq_empty.1 (by grind)
  calc
    measure (Icc 0 1 \ A) = measure F := hFeq.symm
    _ = measure E + measure F := by
      simp [hA.measure_eq_zero_of_measurableSet_subset hEmeas hEsubA]
    _ = measure (E ∪ F) := by
      rw [← measure_union hEF hEmeas]
    _ = measure (Icc 0 1) := by
      rw [Set.diff_union_of_subset Set.inter_subset_right]
    _ = 1 := measure_Icc_zero_one

theorem IsVitali.compl_nonadditive {A : Set ℝ} (hA : IsVitali A) :
    measure (Icc 0 1) ≠ measure A + measure (Icc 0 1 \ A) := by
  apply ne_of_lt
  calc
    measure (Icc 0 1) = 1 := measure_Icc_zero_one
    _ < measure A + 1 := by
      simpa [add_comm] using ENNReal.lt_add_right (by simp) hA.measure_ne_zero
    _ = measure A + measure (Icc 0 1 \ A) := by
      rw [hA.measure_compl_eq_one]

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
  calc
    x - z = (x - y) + (y - z) := by ring
    _ = (q1 : ℝ) + (q2 : ℝ) := by rw [hq1, hq2]
    _ = ((q1 + q2 : ℚ) : ℝ) := by simp

def rationalRelSetoid : Setoid ℝ where
  r x y := rationalRel x y
  iseqv := ⟨fun x ↦ rationalRel_refl x, rationalRel_symm, rationalRel_trans⟩

local instance : Setoid ℝ := rationalRelSetoid

theorem exists_rationalRel_mem_Icc_zero_one (x : ℝ) :
    ∃ y : (Icc 0 1 : Set ℝ), rationalRel x y := by
  obtain ⟨q, hq_left, hq_right⟩ := exists_rat_btwn (sub_one_lt x)
  refine ⟨⟨x - q, by grind⟩, ⟨q, by ring⟩⟩

theorem exists_subtype_mk_eq_quotient (q : Quotient rationalRelSetoid) :
    ∃ y : (Icc 0 1 : Set ℝ), ⟦(y : ℝ)⟧ = q := by
  refine Quotient.inductionOn q ?_
  intro x
  rcases exists_rationalRel_mem_Icc_zero_one x with ⟨y, hy⟩
  exact ⟨y, (Quotient.sound hy).symm⟩

def chosenVitaliPoint (q : Quotient rationalRelSetoid) : (Icc 0 1 : Set ℝ) :=
  Classical.choose (exists_subtype_mk_eq_quotient q)

theorem mk_chosenVitaliPoint (q : Quotient rationalRelSetoid) :
    ⟦(chosenVitaliPoint q : ℝ)⟧ = q :=
  Classical.choose_spec (exists_subtype_mk_eq_quotient q)

def chosenVitali : Set ℝ :=
  Set.range fun q : Quotient rationalRelSetoid ↦ (chosenVitaliPoint q : ℝ)

theorem chosenVitali_subset_Icc_zero_one : chosenVitali ⊆ Icc 0 1 := by
  rintro x ⟨q, rfl⟩
  exact (chosenVitaliPoint q).2

theorem eq_chosenVitaliPoint_of_mem_chosenVitali_of_rationalRel {x y : ℝ}
    (hy : y ∈ chosenVitali) (hxy : rationalRel x y) :
    y = chosenVitaliPoint ⟦x⟧ := by
  rcases hy with ⟨q, rfl⟩
  have hqx :=
    calc
      q = ⟦(chosenVitaliPoint q : ℝ)⟧ := by
        simpa using (mk_chosenVitaliPoint q).symm
      _ = ⟦x⟧ := by simpa using (Quotient.sound hxy).symm
  exact congrArg Subtype.val (congrArg chosenVitaliPoint hqx)

theorem existsUnique_rational_chosenVitali (x : ℝ) : ∃! q : ℚ, x - q ∈ chosenVitali := by
  rcases Quotient.exact (mk_chosenVitaliPoint ⟦x⟧).symm with ⟨q, hq⟩
  refine ⟨q, ⟨⟦x⟧, by grind⟩, ?_⟩
  intro r hr
  have hz : x - r = chosenVitaliPoint ⟦x⟧ :=
    eq_chosenVitaliPoint_of_mem_chosenVitali_of_rationalRel hr ⟨r, by ring⟩
  exact Rat.cast_inj.mp <| calc
    (r : ℝ) = x - (chosenVitaliPoint ⟦x⟧ : ℝ) := by grind
    _ = (q : ℝ) := by grind

theorem isVitali_chosenVitali : IsVitali chosenVitali :=
  ⟨existsUnique_rational_chosenVitali, chosenVitali_subset_Icc_zero_one⟩

theorem exists_not_measurableSet : ∃ A : Set ℝ, ¬ MeasurableSet A :=
  ⟨chosenVitali, isVitali_chosenVitali.not_measurableSet⟩

theorem exists_disjoint_nonadditive :
    ∃ A B : Set ℝ, A ∩ B = ∅ ∧ measure (A ∪ B) ≠ measure A + measure B := by
  refine ⟨chosenVitali, Icc 0 1 \ chosenVitali, by simp, ?_⟩
  simpa [Set.union_diff_cancel chosenVitali_subset_Icc_zero_one] using
    isVitali_chosenVitali.compl_nonadditive

end Real

end MTI

end
