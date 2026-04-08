import Mathlib.Logic.Encodable.Lattice
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Disjointed

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Function MeasurableSpace

variable {X Y Z : Type*}

namespace MTI

section Dynkin

inductive GenDynkin (𝓕 : Set (Set X)) : Set (Set X)
  | basic : ∀ A ∈ 𝓕, GenDynkin 𝓕 A
  | empty : GenDynkin 𝓕 ∅
  | compl : ∀ {a}, GenDynkin 𝓕 a → GenDynkin 𝓕 aᶜ
  | iUnion_nat : ∀ {A : ℕ → Set X},
    Pairwise (Disjoint on A) → (∀ i, GenDynkin 𝓕 (A i)) → GenDynkin 𝓕 (⋃ i, A i)

@[simp, grind .]
theorem genDynkin_empty {𝓕 : Set (Set X)} : ∅ ∈ GenDynkin 𝓕 :=
  GenDynkin.empty

@[grind .]
theorem genDynkin_basic {𝓕 : Set (Set X)} {A : Set X} (hA : A ∈ 𝓕) :
    A ∈ GenDynkin 𝓕 :=
  GenDynkin.basic A hA

@[grind .]
theorem genDynkin_compl {𝓕 : Set (Set X)} {A : Set X} (hA : A ∈ GenDynkin 𝓕) :
    Aᶜ ∈ GenDynkin 𝓕 :=
  GenDynkin.compl hA

theorem genDynkin_iUnion_nat {𝓕 : Set (Set X)} {A : ℕ → Set X}
    (h_disj : Pairwise (Disjoint on A)) (hf : ∀ i, A i ∈ GenDynkin 𝓕) :
    ⋃ i, A i ∈ GenDynkin 𝓕 :=
  GenDynkin.iUnion_nat h_disj hf

theorem genDynkin_iUnion {𝓕 : Set (Set X)} {ι : Type*} [Countable ι] {A : ι → Set X}
    (h_disj : Pairwise (Disjoint on A)) (hf : ∀ i, A i ∈ GenDynkin 𝓕) :
    ⋃ i, A i ∈ GenDynkin 𝓕 := by
  cases nonempty_encodable ι
  rw [← Encodable.iUnion_decode₂]
  apply genDynkin_iUnion_nat
  · intro i j hij A' hAi hAj x hx
    have hAi := hAi hx
    have hAj := hAj hx
    simp only [Option.mem_def, mem_iUnion, exists_prop] at hAi hAj
    have ⟨i', hi', hi''⟩ := hAi
    have ⟨j', hj', hj''⟩ := hAj
    have hij' : i' ≠ j' := by
      intro h
      apply hij
      rw [Encodable.decode₂_eq_some] at hi' hj'
      grind
    exact h_disj hij' inter_subset_left inter_subset_right (mem_inter hi'' hj'')
  · intro n
    simp only [Option.mem_def]
    by_cases h : ∃ i : ι, Encodable.encode i = n
    · rcases h with ⟨i, hi⟩
      rw [← hi]
      simp only [Encodable.decode₂_encode, Option.some.injEq, iUnion_iUnion_eq_right]
      exact hf i
    · simp_rw [← Encodable.decode₂_eq_some] at h
      suffices ⋃ b, ⋃ (_ : Encodable.decode₂ ι n = some b), A b = ∅ by
        rw [this]
        exact genDynkin_empty
      simp only [iUnion_eq_empty]
      intro i hi
      grind

@[grind .]
theorem genDynkin_union {𝓕 : Set (Set X)} {A B : Set X}
    (h_disj : Disjoint A B) (hA : A ∈ GenDynkin 𝓕) (hB : B ∈ GenDynkin 𝓕) :
    A ∪ B ∈ GenDynkin 𝓕 := by
  let f : Bool → Set X := fun b => if b then A else B
  have : ⋃ b, f b = A ∪ B := by
    ext x
    rw [mem_iUnion, Bool.exists_bool]
    grind
  rw [← this]
  apply genDynkin_iUnion
  · intro i j hij
    cases i <;> cases j <;> grind
  · intro b
    cases b with
    | true => apply hA
    | false => apply hB

theorem pairwise_disjoint_inter_left {f : ℕ → Set X}
    (hdf : Pairwise (Disjoint on f)) (A : Set X) :
    Pairwise (Disjoint on fun i => A ∩ f i) := by
  intro i j hij
  exact (hdf hij).mono inter_subset_right inter_subset_right

theorem pairwise_disjoint_inter_right {f : ℕ → Set X}
    (hdf : Pairwise (Disjoint on f)) (A : Set X) :
    Pairwise (Disjoint on fun i => f i ∩ A) := by
  intro i j hij
  exact (hdf hij).mono inter_subset_left inter_subset_left

@[grind .]
theorem genDynkin_inter_compl_right {𝓕 : Set (Set X)} {A B : Set X}
  (hA : A ∈ GenDynkin 𝓕) (hAB : A ∩ B ∈ GenDynkin 𝓕) :
    A ∩ Bᶜ ∈ GenDynkin 𝓕 := by
  have : A ∩ Bᶜ = (Aᶜ ∪ (A ∩ B))ᶜ := by grind
  grind

@[grind .]
theorem genDynkin_inter_compl_left {𝓕 : Set (Set X)} {A B : Set X}
  (hB : B ∈ GenDynkin 𝓕) (hAB : A ∩ B ∈ GenDynkin 𝓕) :
    Aᶜ ∩ B ∈ GenDynkin 𝓕 := by
  rw [inter_comm]
  grind

theorem genDynkin_inter {𝓕 : Set (Set X)} (h𝓕 : ∀ ⦃A B⦄, A ∈ 𝓕 → B ∈ 𝓕 → A ∩ B ∈ 𝓕)
    {A B : Set X} (hA : A ∈ GenDynkin 𝓕) (hB : B ∈ GenDynkin 𝓕) : A ∩ B ∈ GenDynkin 𝓕 := by
  induction hA with
  | basic A hA =>
    induction hB with
    | basic B hB => exact genDynkin_basic (h𝓕 hA hB)
    | empty => simp
    | @compl B hB ih => grind
    | @iUnion_nat f hdf hf ih =>
      simpa [inter_iUnion] using genDynkin_iUnion (pairwise_disjoint_inter_left hdf A) ih
  | empty => simp
  | @compl A hA ih => grind
  | @iUnion_nat f hdf hf ih =>
    simpa [iUnion_inter] using genDynkin_iUnion (pairwise_disjoint_inter_right hdf B) ih

theorem measurableSet_iff_mem_genDynkin [MeasurableSpace X] {𝓕 : Set (Set X)}
    (h : ‹_› = generateFrom 𝓕) (h𝓕 : ∀ ⦃A B⦄, A ∈ 𝓕 → B ∈ 𝓕 → A ∩ B ∈ 𝓕) (A : Set X) :
    MeasurableSet A ↔ A ∈ GenDynkin 𝓕 := by
  apply Iff.intro
  · intro hA
    rw [h] at hA
    induction hA with
    | basic A hA => grind
    | empty => grind
    | @compl A hA ih => grind
    | @iUnion f hf ih =>
      rw [← iUnion_disjointed]
      apply genDynkin_iUnion (disjoint_disjointed f)
      intro n
      apply disjointedRec _ (ih n)
      intro A n hA
      rw [@diff_eq]
      apply genDynkin_inter h𝓕 hA (genDynkin_compl (ih n))
  · intro hA
    induction hA with
    | basic A hA => apply h ▸ measurableSet_generateFrom hA
    | empty => apply MeasurableSet.empty
    | @compl A hA ih => apply MeasurableSet.compl ih
    | @iUnion_nat f hdf hf ih => apply MeasurableSet.iUnion ih

@[elab_as_elim]
theorem induction_on_inter
    [m : MeasurableSpace X] {P : ∀ A : Set X, MeasurableSet A → Prop}
    {𝓕 : Set (Set X)} (h_eq : m = generateFrom 𝓕) (h_inter : ∀ ⦃A B⦄, A ∈ 𝓕 → B ∈ 𝓕 → A ∩ B ∈ 𝓕)
    (empty : P ∅ .empty)
    (basic : ∀ A (hA : A ∈ 𝓕), P A <| h_eq ▸ measurableSet_generateFrom hA)
    (compl : ∀ A (hAm : MeasurableSet A), P A hAm → P Aᶜ hAm.compl)
    (iUnion : ∀ (A : ℕ → Set X), Pairwise (Disjoint on A) → ∀ (hAm : ∀ i, MeasurableSet (A i)),
      (∀ i, P (A i) (hAm i)) → P (⋃ i, A i) (.iUnion hAm))
    (A : Set X) (hA : MeasurableSet A) :
    P A hA := by
  have hA' := (measurableSet_iff_mem_genDynkin h_eq h_inter A).mp hA
  induction hA' using GenDynkin.rec with
  | basic A hA' => exact basic A hA'
  | empty => exact empty
  | @compl A hA' ih =>
    apply compl A ((measurableSet_iff_mem_genDynkin h_eq h_inter A).mpr hA') (ih _)
  | @iUnion_nat A hAd hA' ih =>
    apply iUnion _ hAd _ (fun n ↦ ih n _)
    intro n
    apply (measurableSet_iff_mem_genDynkin h_eq h_inter (A n)).mpr (hA' n)

end Dynkin

end MTI
