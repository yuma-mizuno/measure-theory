import MeasureTheory.Lean.Lebesgue.OuterMeasure

set_option autoImplicit false

open Topology ENNReal Set Function

noncomputable section

namespace MTI

namespace Real

inductive MeasurableSet : Set ℝ → Prop
  | ici' : ∀ a : ℝ, MeasurableSet (Ici a)
  | empty' : MeasurableSet ∅
  | compl' : ∀ A, MeasurableSet A → MeasurableSet Aᶜ
  | iUnion' : ∀ A : ℕ → Set ℝ, (∀ n, MeasurableSet (A n)) → MeasurableSet (⋃ i, A i)

theorem MeasurableSet.ici (a : ℝ) : MeasurableSet (Ici a) :=
  MeasurableSet.ici' a

@[simp]
theorem MeasurableSet.empty : MeasurableSet (∅ : Set ℝ) :=
  MeasurableSet.empty'

theorem MeasurableSet.compl {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet Aᶜ :=
  MeasurableSet.compl' A hA

theorem MeasurableSet.iUnion (A : ℕ → Set ℝ) (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet (⋃ i, A i) :=
  MeasurableSet.iUnion' A hA

theorem MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ) := by
  simpa using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ)).compl

lemma MeasurableSet.iUnion_countable {ι : Type} [Countable ι] {A : ι → Set ℝ}
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (⋃ i, A i) := by
  cases isEmpty_or_nonempty ι
  · simp [MeasurableSet.empty]
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iUnion_congr_of_surjective _ he (fun _ => rfl)]
    exact MeasurableSet.iUnion _ fun _ => hA _

theorem MeasurableSet.biUnion {ι : Type} {f : ι → Set ℝ} {s : Set ι} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) := by
  rw [biUnion_eq_iUnion]
  have := hs.to_subtype
  exact MeasurableSet.iUnion_countable (by simpa using h)

theorem MeasurableSet.iInter {A : ℕ → Set ℝ} (hA : ∀ n, MeasurableSet (A n)) :
    MeasurableSet (⋂ n, A n) := by
  have hEq : (⋂ n, A n) = (⋃ n, (A n)ᶜ)ᶜ := by
    ext x
    simp
  rw [hEq]
  exact (MeasurableSet.iUnion _ fun n ↦ (hA n).compl).compl

theorem MeasurableSet.union {A₁ A₂ : Set ℝ} (h₁ : MeasurableSet A₁) (h₂ : MeasurableSet A₂) :
    MeasurableSet (A₁ ∪ A₂) := by
  rw [union_eq_iUnion]
  exact MeasurableSet.iUnion_countable (Bool.forall_bool.2 ⟨h₂, h₁⟩)

theorem MeasurableSet.inter {A₁ A₂ : Set ℝ} (h₁ : MeasurableSet A₁) (h₂ : MeasurableSet A₂) :
    MeasurableSet (A₁ ∩ A₂) := by
  rw [(by grind : A₁ ∩ A₂ = (A₁ᶜ ∪ A₂ᶜ)ᶜ)]
  apply (h₁.compl.union h₂.compl).compl

theorem MeasurableSet.diff {A₁ A₂ : Set ℝ} (h₁ : MeasurableSet A₁) (h₂ : MeasurableSet A₂) :
    MeasurableSet (A₁ \ A₂) := by
  rw [diff_eq]
  exact h₁.inter h₂.compl

theorem measurableSet_Ici (a : ℝ) : MeasurableSet (Set.Ici a) := by
  apply MeasurableSet.ici

theorem measurableSet_Iio (a : ℝ) : MeasurableSet (Set.Iio a) := by
  rw [← Set.compl_Ici]
  apply MeasurableSet.compl
  apply MeasurableSet.ici

theorem measurableSet_Ioi (a : ℝ) : MeasurableSet (Set.Ioi a) := by
  rcases TopologicalSpace.isOpen_biUnion_countable (Set.Ioi a) Set.Ioi fun _ _ ↦ isOpen_Ioi
    with ⟨A, haA, hAc, hAU⟩
  have : Set.Ioi a = ⋃ b ∈ A, Set.Ici b := by
    refine Subset.antisymm ?_ <| iUnion₂_subset fun b hb ↦ by grind
    refine Subset.trans ?_ <| iUnion₂_mono fun _ _ ↦ Set.Ioi_subset_Ici_self
    simp only [hAU, mem_Ioi, subset_def, mem_iUnion, exists_prop]
    intro b hab
    exact exists_between hab
  simp only [this]
  apply MeasurableSet.biUnion hAc
  intro a ha
  exact measurableSet_Ici a

theorem measurableSet_Iic (a : ℝ) : MeasurableSet (Set.Iic a) := by
  rw [← Set.compl_Ioi]
  apply MeasurableSet.compl
  exact measurableSet_Ioi a

theorem measurableSet_Ioc (a b : ℝ) : MeasurableSet (Set.Ioc a b) := by
  have : Set.Ioc a b = Set.Ioi a ∩ Set.Iic b := by grind
  rw [this]
  apply (measurableSet_Ioi a).inter (measurableSet_Iic b)

theorem measurableSet_Ico (a b : ℝ) : MeasurableSet (Set.Ico a b) := by
  have : Set.Ico a b = Set.Ici a ∩ Set.Iio b := by grind
  rw [this]
  apply (measurableSet_Ici a).inter (measurableSet_Iio b)

theorem measurableSet_Icc (a b : ℝ) : MeasurableSet (Set.Icc a b) := by
  have : Set.Icc a b = Set.Iic b ∩ Set.Ici a := by grind
  rw [this]
  apply (measurableSet_Iic b).inter (measurableSet_Ici a)

theorem measurableSet_Ioo (a b : ℝ) : MeasurableSet (Set.Ioo a b) := by
  have : Set.Ioo a b = Set.Ioi a ∩ Set.Iio b := by grind
  rw [this]
  apply (measurableSet_Ioi a).inter (measurableSet_Iio b)

theorem measurableSet_singleton (a : ℝ) : MeasurableSet ({a} : Set ℝ) := by
  have : ({a} : Set ℝ) = Set.Iic a ∩ Set.Ici a := by grind
  rw [this]
  apply (measurableSet_Iic a).inter (measurableSet_Ici a)

end Real

end MTI

end
