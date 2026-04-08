/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!

-/

@[expose] public section


noncomputable section

open ENNReal Set Filter
open MeasureTheory

variable {α β : Type*}

namespace Playground

variable {X Y Z : Type*}

namespace Measure

variable [MeasurableSpace X] [MeasurableSpace Y]

def map (f : X → Y) (hf : Measurable f) (μ : Measure X) : Measure Y :=
  Measure.ofMeasurable (fun (A : Set Y) hs ↦ μ (f ⁻¹' A)) (by simp) <| by
    intro A hA hAd
    dsimp only
    simp only [preimage_iUnion]
    apply measure_iUnion _ (fun i ↦ hf (hA i))
    intro i j hij
    have := hAd hij
    grind

@[simp]
theorem map_apply (f : X → Y) (hf : Measurable f) (μ : Measure X) (A : Set Y)
    (hA : MeasurableSet A) : map f hf μ A = μ (f ⁻¹' A) :=
  Measure.ofMeasurable_apply _ hA

theorem map_lintegral (f : X → Y) (hf : Measurable f)
    (μ : Measure X) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂map f hf μ = ∫⁻ x, g (f x) ∂μ := by
  let h n : SimpleFunc X ℝ≥0∞ := {
    toFun := (SimpleFunc.eapprox g n) ∘ f
    measurableSet_fiber' := fun a ↦ by
      apply (SimpleFunc.measurable (SimpleFunc.eapprox g n)).comp hf
      exact MeasurableSet.singleton a
    finite_range' := by
      rw [@range_comp]
      have : (⇑(SimpleFunc.eapprox g n) '' range f) ⊆ range (SimpleFunc.eapprox g n) := by
        exact image_subset_range (⇑(SimpleFunc.eapprox g n)) (range f)
      clear hf hg
      apply Set.Finite.subset _ this
      exact SimpleFunc.finite_range (SimpleFunc.eapprox g n) }
  calc
    ∫⁻ (y : Y), g y ∂map f hf μ = ⨆ n, ∫⁻ (y : Y), (SimpleFunc.eapprox g n) y ∂map f hf μ := by
      rw [lintegral_eq_iSup_eapprox_lintegral hg]
      apply iSup_congr
      intro n
      rw [@SimpleFunc.lintegral_eq_lintegral]
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * map f hf μ ((SimpleFunc.eapprox g n) ⁻¹' {a}) := by
      apply iSup_congr
      intro n
      rw [← @SimpleFunc.map_lintegral]
      rw [@SimpleFunc.lintegral_eq_lintegral]
      rfl
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * μ (f ⁻¹' ((SimpleFunc.eapprox g n) ⁻¹' {a})) := by
      apply iSup_congr
      intro n
      congr 1 with a
      congr 1
      rw [map_apply]
      exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox g n) a
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * μ ((SimpleFunc.eapprox g n ∘ f) ⁻¹' {a}) := by
      rfl
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox g n).range,
        a * μ (h n ⁻¹' {a}) := by
      rfl
    _ = ⨆ n, ∑ a ∈ (h n).range, a * μ (h n ⁻¹' {a}) := by
      congr 1 with n
      apply Eq.symm
      apply Finset.sum_subset
      · intro a
        simp only [SimpleFunc.mem_range, mem_range, forall_exists_index]
        intro x hx
        refine ⟨f x, ?_⟩
        rw [← hx]
        rfl
      · intro a
        simp only [SimpleFunc.mem_range, mem_range, not_exists, mul_eq_zero, forall_exists_index]
        intro y hy ha
        right
        -- rw [← SimpleFunc.eapprox_comp hg hf]
        have : (h n) ⁻¹' {a} = ∅ := by
          ext x
          simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
          apply ha
        rw [this]
        simp
    _ = ⨆ n, ∫⁻ (x : X), (h n) x ∂μ := by
      apply iSup_congr
      intro n
      rw [@SimpleFunc.lintegral_eq_lintegral]
      rw [SimpleFunc.lintegral]
    _ = ∫⁻ (x : X), (g ∘ f) x ∂μ := by
      rw [← lintegral_iSup]
      · apply lintegral_congr
        intro x
        simp only [SimpleFunc.coe_mk, Function.comp_apply, h]
        rw [SimpleFunc.iSup_eapprox_apply hg (f x)]
      · exact fun n ↦ SimpleFunc.measurable (h n)
      · intro i j hij x
        simp only [SimpleFunc.coe_mk, Function.comp_apply, h]
        apply SimpleFunc.monotone_eapprox g hij



end Measure

def OuterMeasure.restrict (μ : OuterMeasure X) (A : Set X) : OuterMeasure X where
  measureOf B := μ (A ∩ B)
  empty := by simp
  mono := by
    intro A B hAB
    apply μ.mono
    simp only [Set.inter_subset_inter_right, hAB]
  iUnion_nat := by
    intro B hBd
    rw [Set.inter_iUnion]
    exact measure_iUnion_le fun i ↦ A ∩ B i

theorem OuterMeasure.restrict_apply (μ : OuterMeasure X) (A B : Set X) :
    OuterMeasure.restrict μ A B = μ (A ∩ B) :=
  rfl

variable [MeasurableSpace X]

def Measure.restrict (μ : Measure X) (A : Set X) : Measure X :=
  OuterMeasure.toMeasure (OuterMeasure.restrict μ.toOuterMeasure A) <| by
    intro B hB C
    simp only [OuterMeasure.restrict_apply, Measure.coe_toOuterMeasure]
    calc
      μ (A ∩ C) = μ ((A ∩ C) ∩ B) + μ ((A ∩ C) \ B) := by
        apply le_toOuterMeasure_caratheodory _ _ hB
      _ = μ (A ∩ (C ∩ B)) + μ (A ∩ (C \ B)) := by
        congr 2
        · grind
        · grind



theorem restrict_toOuterMeasure_eq_toOuterMeasure_restrict
    (μ : Measure X) (A : Set X) (h : MeasurableSet A) :
    (Measure.restrict μ A).toOuterMeasure = OuterMeasure.restrict μ.toOuterMeasure A := by
  simp_rw [Measure.restrict]
  conv_rhs => rw [← μ.trimmed]
  apply le_antisymm
  · intro B
    rw [OuterMeasure.restrict_apply]
    rcases μ.exists_measurable_superset_eq_trim (A ∩ B) with ⟨C, hCAB, hC, hμC⟩
    rw [← hμC]
    rw [inter_comm] at hCAB
    rw [inter_subset] at hCAB
    apply (measure_mono hCAB).trans
    simp only [toMeasure_toOuterMeasure, Measure.coe_toOuterMeasure]
    rw [OuterMeasure.trim_eq _ (h.compl.union hC)]
    rw [OuterMeasure.restrict_apply]
    simp only [Measure.coe_toOuterMeasure]
    apply measure_mono
    grind
  · intro B
    apply OuterMeasure.le_trim_iff.2
    intro C hC
    rw [OuterMeasure.restrict_apply]
    rw [OuterMeasure.trim_eq _ (h.inter hC)]
    rw [OuterMeasure.restrict_apply]



-- , OuterMeasure.restrict_trim h, μ.trimmed

-- theorem Measure.restrict_apply (μ : Measure X) (A B : Set X) (hA : MeasurableSet A) :
--     Measure.restrict μ A B = μ (A ∩ B) := by
--   rw [Measure.restrict]
--   rw [← Measure.toOuterMeasure_apply]
--   sorry

def Measure.restrict' (μ : Measure X) (A : Set X) (hA : MeasurableSet A) : Measure X :=
  Measure.ofMeasurable (fun B hB ↦ μ (A ∩ B)) (by simp) <| by
    intro B hB hdB
    dsimp only
    rw [Set.inter_iUnion]
    refine measure_iUnion ?_ ?_
    · intro i j hij C hCi hCj
      simp only [le_eq_subset, subset_inter_iff] at hCi hCj
      intro hCA
      apply hdB hij hCi.2 hCj.2
    · intro i
      apply hA.inter (hB i)

theorem Measure.restrict'_apply (μ : Measure X) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.restrict' μ A hA) B = μ (A ∩ B) := by
  rw [Measure.restrict']
  rw [Measure.ofMeasurable_apply _ hB]

theorem restrict'_toOuterMeasure_eq_toOuterMeasure_restrict
    (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    (Measure.restrict μ A).toOuterMeasure = OuterMeasure.restrict μ.toOuterMeasure A := by
  simp_rw [Measure.restrict]
  conv_rhs => rw [← μ.trimmed]
  apply le_antisymm
  · intro B
    rw [OuterMeasure.restrict_apply]
    rcases μ.exists_measurable_superset_eq_trim (A ∩ B) with ⟨C, hCAB, hC, hμC⟩
    rw [← hμC]
    rw [inter_comm] at hCAB
    rw [inter_subset] at hCAB
    apply (measure_mono hCAB).trans
    simp only [toMeasure_toOuterMeasure, Measure.coe_toOuterMeasure]
    rw [OuterMeasure.trim_eq _ (hA.compl.union hC)]
    rw [OuterMeasure.restrict_apply]
    simp only [Measure.coe_toOuterMeasure]
    apply measure_mono
    grind
  · intro B
    apply OuterMeasure.le_trim_iff.2
    intro C hC
    rw [OuterMeasure.restrict_apply]
    rw [OuterMeasure.trim_eq _ (hA.inter hC)]
    rw [OuterMeasure.restrict_apply]

theorem restrict''_toOuterMeasure_eq_toOuterMeasure_restrict
    (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    (Measure.restrict' μ A hA).toOuterMeasure = OuterMeasure.restrict μ.toOuterMeasure A := by
  -- simp_rw [Measure.restrict']
  -- conv_rhs => rw [← μ.trimmed]
  -- simp_rw [Measure.restrict]
  -- conv_rhs => rw [← μ.trimmed]
  apply le_antisymm
  · intro B
    rw [OuterMeasure.restrict_apply]
    rcases μ.exists_measurable_superset_eq_trim (A ∩ B) with ⟨C, hCAB, hC, hμC⟩
    rw [← measure_eq_trim] at hμC
    simp only [Measure.coe_toOuterMeasure]
    rw [← hμC]
    rw [inter_comm] at hCAB
    rw [inter_subset] at hCAB
    apply (measure_mono hCAB).trans
    simp only [Measure.coe_toOuterMeasure]
    -- rw [OuterMeasure.trim_eq _ (hA.compl.union hC)]
    rw [Measure.restrict'_apply _ _ (hA.compl.union hC)]
    -- simp only [Measure.coe_toOuterMeasure]
    apply le_trans (le_of_eq _) (measure_mono (show A ∩ C ⊆ C from Set.inter_subset_right))
    congr 1
    grind
  · intro B
    simp only [Measure.coe_toOuterMeasure]
    rw [measure_eq_iInf]
    apply le_iInf
    intro C
    apply le_iInf
    intro hBC
    apply le_iInf
    intro hC
    rw [Measure.restrict'_apply _ _ hC]
    rw [@OuterMeasure.restrict_apply]
    -- rw [← @measure_eq_trim]
    apply measure_mono
    grind

example (μ : Measure X) (A : Set X) (hA : MeasurableSet A) (B : Set X) :
    (Measure.restrict' μ A hA) B = μ (A ∩ B) := by
  apply le_antisymm
  · rcases μ.exists_measurable_superset_eq_trim (A ∩ B) with ⟨C, hCAB, hC, hμC⟩
    rw [← measure_eq_trim] at hμC
    -- simp only [Measure.coe_toOuterMeasure]
    rw [← hμC]
    rw [inter_comm] at hCAB
    rw [inter_subset] at hCAB
    apply (measure_mono hCAB).trans
    simp only [Measure.coe_toOuterMeasure]
    -- rw [OuterMeasure.trim_eq _ (hA.compl.union hC)]
    rw [Measure.restrict'_apply _ _ (hA.compl.union hC)]
    -- simp only [Measure.coe_toOuterMeasure]
    apply le_trans (le_of_eq _) (measure_mono (show A ∩ C ⊆ C from Set.inter_subset_right))
    congr 1
    grind
  · conv_rhs => rw [measure_eq_iInf]
    apply le_iInf
    intro C
    apply le_iInf
    intro hBC
    apply le_iInf
    intro hC
    rw [Measure.restrict'_apply _ _ hC]
    apply measure_mono
    grind


open Classical in
def OuterMeasure.dirac (x : X) : OuterMeasure X where
  measureOf A := indicator A (fun _ => 1) x
  empty := by simp
  mono := by
    intro A B hAB
    rw [indicator_apply]
    rw [indicator_apply]
    by_cases hx : x ∈ A
    · rw [if_pos hx, if_pos (hAB hx)]
    · rw [if_neg hx]
      apply zero_le
  iUnion_nat := by
    intro A hAd
    calc (⋃ i, A i).indicator (fun x ↦ (1 : ℝ≥0∞)) x
      _ = ⨆ i, (A i).indicator (fun x ↦ (1 : ℝ≥0∞)) x := by
        by_cases hx : x ∈ ⋃ i, A i
        · have ⟨i, hi⟩ := hx
          simp only [indicator_apply]
          rw [if_pos hx]
          rw [mem_iUnion] at hx
          apply le_antisymm
          · have ⟨i, hi⟩ := hx
            apply le_iSup_of_le i
            rw [if_pos hi]
          · apply iSup_le
            intro n
            apply ite_le_one (by simp) (by simp)
        · simp only [indicator_apply]
          rw [if_neg hx]
          suffices (⨆ i, if x ∈ A i then 1 else 0 : ℝ≥0∞) = 0 by
            rw [this]
          simp only [iSup_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false]
          intro n
          simp only [mem_iUnion, not_exists] at hx
          apply hx
      _ ≤ ∑' (i : ℕ), (A i).indicator (fun x ↦ (1 : ℝ≥0∞)) x := by
        apply iSup_le
        intro n
        apply ENNReal.le_tsum

@[simp]
theorem OuterMeasure.dirac_apply {X : Type*} (x : X) (A : Set X) :
    OuterMeasure.dirac x A = indicator A (fun _ => 1) x :=
  rfl

variable [MeasurableSpace Y] [MeasurableSpace Z]

def Measure.dirac (x : X) : Measure X :=
  OuterMeasure.toMeasure (OuterMeasure.dirac x) <| by
    intro A _ B
    by_cases hB : x ∈ B
    · by_cases hA : x ∈ A
      · simp [hA, hB]
      · simp [hA, hB]
    · simp [hB]
    -- by_cases ht : x ∈ t <;> by_cases hs : x ∈ s
    -- · simp [ht, hs]
    -- · simp [ht, hs]
    -- · simp [ht, hs]
    -- · simp [ht, hs]
    -- simp [*]

def Measure.dirac' (x : X) : Measure X :=
  Measure.ofMeasurable (fun A _ ↦ indicator A (fun _ => 1) x) (by simp) <| by
    intro A hA hAd
    simp only
    by_cases hx : x ∈ (⋃ i, A i)
    · rw [indicator_of_mem hx]
      simp only [mem_iUnion] at hx
      have ⟨i, hi⟩ := hx
      have : ∑' (i : ℕ), (A i).indicator (fun x ↦ (1 : ℝ≥0∞)) x =
          (A i).indicator (fun x ↦ (1 : ℝ≥0∞)) x +
            ∑' k : ℕ, if k = i then 0 else (A k).indicator (fun x ↦ (1 : ℝ≥0∞)) x := by
        convert tsum_eq_add_tsum_ite (f := fun i ↦ (A i).indicator (fun x ↦ (1 : ℝ≥0∞)) x) i
      rw [this]
      rw [indicator_of_mem hi]
      suffices (∑' k : ℕ, if k = i then 0 else (A k).indicator (fun x ↦ (1 : ℝ≥0∞)) x) = 0 by
        rw [this]
        simp
      refine ENNReal.tsum_eq_zero.mpr ?_
      intro k
      simp only [ite_eq_left_iff, indicator_apply_eq_zero, one_ne_zero, imp_false]
      intro hik hAk
      have hx : x ∈ A i ∩ A k := by
        exact mem_inter hi hAk
      apply hAd hik _ _ hx
      · simp
      · simp
    · rw [indicator_of_notMem hx]
      simp only [mem_iUnion, not_exists] at hx
      symm
      refine ENNReal.tsum_eq_zero.mpr ?_
      intro i
      rw [indicator_of_notMem (hx i)]


@[simp]
theorem Measure.dirac_apply (x : X) (A : Set X) (hA : MeasurableSet A) :
    Measure.dirac x A = indicator A (fun _ => 1) x := by
  rw [Measure.dirac, toMeasure_apply _ _ hA, OuterMeasure.dirac_apply]

@[simp]
theorem Measure.dirac_apply₀ (x : X) (A : Set X) (hA : NullMeasurableSet A (Measure.dirac x)) :
    Measure.dirac x A = indicator A (fun _ => 1) x := by
  have ⟨B, hBA, hB, hB'⟩ := NullMeasurableSet.exists_measurable_superset_ae_eq hA
  rw [Measure.dirac]
  rw [toMeasure_apply₀ (OuterMeasure.dirac x) _ hA]
  rw [OuterMeasure.dirac_apply]


example {a : X} {f : X → ℝ≥0∞}
    (hf : Measurable f) : MeasurableSet {x | f x = f a} := by
  have : {x | f x = f a} = f ⁻¹' Iic (f a) ∩ f ⁻¹' Ici (f a) := by
    ext x
    grind
  rw [this]
  refine MeasurableSet.inter ?_ ?_
  · apply hf measurableSet_Iic
  · apply hf measurableSet_Ici

theorem ae_eq_dirac' {a : X} {f : X → ℝ≥0∞} (hf : Measurable f) :
    f =ᵐ[Measure.dirac a] Function.const X (f a) := by
  change ∀ᵐ x ∂(Measure.dirac a), f x = f a
  suffices MeasurableSet { x | f x = f a } from by
    rw [ae_iff]
    calc
      (Measure.dirac a) {x | ¬f x = f a} = (Measure.dirac a) {x | f x = f a}ᶜ := by grind
      _ = 0 := by
        rw [measure_compl this]
        · rw [Measure.dirac_apply a _ this]
          rw [Measure.dirac_apply _ _ MeasurableSet.univ]
          rw [indicator_of_mem (mem_univ _)]
          rw [indicator_of_mem (by grind)]
          rw [tsub_self]
        · rw [Measure.dirac_apply a _ this]
          simp
  refine measurableSet_eq_fun hf measurable_const

theorem lintegral_dirac (a : X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂Measure.dirac a = f a :=
  calc
    ∫⁻ x, f x ∂Measure.dirac a = ∫⁻ x, f a ∂Measure.dirac a :=
      lintegral_congr_ae (ae_eq_dirac' hf)
    _ = (SimpleFunc.const _ (f a)).lintegral (Measure.dirac a) := by
      rw [← SimpleFunc.lintegral_eq_lintegral]
      apply lintegral_congr
      intro x
      simp
    _ = ∑ x ∈ (SimpleFunc.const X (f a)).range,
        x * (Measure.dirac a) ((SimpleFunc.const X (f a)) ⁻¹' {x}) := by
      rw [SimpleFunc.lintegral]
    _ = ∑ x ∈ (SimpleFunc.const X (f a)).range,
        x * indicator ((SimpleFunc.const X (f a)) ⁻¹' {x}) (fun _ => 1) a := by
      congr 1
      ext x
      congr 1
      apply Measure.dirac_apply a
      exact SimpleFunc.measurableSet_fiber (SimpleFunc.const X (f a)) x
    _ = f a * ((Measure.dirac a) univ) := by
      cases isEmpty_or_nonempty X
      · simp [(Measure.dirac a).eq_zero_of_isEmpty]
      · simp
    _ = f a := by simp

-- theorem Measure.dirac_preimage (x : X) :
--     Measure.dirac y ∘ f ⁻¹' = Measure.dirac (Classical.choose (f ⁻¹' {y})) := by
--   ext A hA
--   rw [Measure.dirac_apply _ A hA, Measure.dirac_apply _ (f ⁻¹' A) (hf hA)]
--   simp only [indicator_apply]
--   by_cases hy : y ∈ A
--   · have : Classical.choose (f ⁻¹' {y}) ∈ f ⁻¹' A := by
--       simp only [mem_preimage, mem_singleton_iff]
--       exact hy
--     simp [this]
--   · simp [hy]

inductive Measure.MeasurableGen (X : Type*) [MeasurableSpace X] : Set (Set (Measure X))
  | proj (A : Set X) (hs : MeasurableSet A) (B : Set ℝ≥0∞) (hB : MeasurableSet B) :
      Measure.MeasurableGen X ({μ | μ A ∈ B})

instance Measure.instMeasurableSpace : MeasurableSpace (Measure X) :=
  MeasurableSpace.generateFrom (Measure.MeasurableGen X)

theorem Measure.measurable_coe {A : Set X} (hA : MeasurableSet A) :
    Measurable fun μ : Measure X => μ A :=
  fun {B} hB ↦ MeasurableSpace.measurableSet_generateFrom (MeasurableGen.proj A hA B hB)

@[fun_prop]
theorem Measure.measurable_lintegral {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure X => ∫⁻ x, f x ∂μ := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n => Finset.measurable_fun_sum _ fun i _ => ?_
  refine Measurable.const_mul ?_ _
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)

theorem measurable_of_measurable_coe (μ : X → Measure Y)
    (h : ∀ (s : Set Y), MeasurableSet s → Measurable fun b ↦ μ b s) : Measurable μ := by
  intro s hs
  induction hs with
  | basic s hs =>
    obtain ⟨s, hs, t, ht⟩ := hs
    simp only [preimage_setOf_eq, measurableSet_setOf]
    exact measurableSet_setOf.mp (h s hs ht)
  | empty => simp
  | compl s hs ih =>
    rw [@preimage_compl]
    apply ih.compl
  | iUnion A hAd ihA =>
    rw [@preimage_iUnion]
    apply MeasurableSet.iUnion ihA

    -- iSup₂_le fun s hs =>
    --   MeasurableSpace.comap_le_iff_le_map.2 <| by
    --     rw [MeasurableSpace.map_comp]

    --     exact h _ _


theorem Measure.dirac_measurable : Measurable (Measure.dirac : X → Measure X) := by
  intro A hA
  induction hA with
  | basic A hA =>
    rcases hA with ⟨A, hA, B, hB⟩
    have : MeasurableSet ((indicator A (fun _ ↦ (1 : ℝ≥0∞))) ⁻¹' B)  :=
      measurable_const.indicator hA hB
    apply MeasurableSet.congr this
    simp only [preimage_setOf_eq, dirac_apply _ _ hA]
    grind
  | empty => simp
  | compl A hA ih =>
    simp only [preimage_compl]
    apply ih.compl
  | iUnion A hA ih =>
    simp only [preimage_iUnion]
    apply MeasurableSet.iUnion ih

def Measure.join (m : Measure (Measure X)) : Measure X :=
  Measure.ofMeasurable (fun s _ ↦ ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
    (by
      intro f hf h
      dsimp only
      apply (lintegral_congr (fun μ ↦ measure_iUnion h hf)).trans
      apply lintegral_tsum (fun i ↦ Measurable.aemeasurable ?_)
      exact measurable_coe (hf i))

def Measure.bind' (f : X → Measure Y) (hf : Measurable f) (μ : Measure X) : Measure Y :=
  Measure.join (Measure.map f hf μ)

open Classical in
def Measure.bind (f : X → Measure Y) (μ : Measure X) : Measure Y :=
  if hf : Measurable f then
    Measure.ofMeasurable (fun A _ ↦ ∫⁻ x, f x A ∂μ) (by simp) <| fun A hA hAd ↦
      calc
      ∫⁻ (x : X), (f x) (⋃ i, A i) ∂μ
      _ = ∫⁻ (x : X), ∑' (i : ℕ), (f x) (A i) ∂μ :=
        lintegral_congr (fun x ↦ measure_iUnion hAd hA)
      _ = ∑' (i : ℕ), ∫⁻ (x : X), (f x) (A i) ∂μ :=
        lintegral_tsum (fun n ↦ ((Measure.measurable_coe (hA n)).comp hf).aemeasurable)
  else 0

@[simp]
theorem Measure.bind_apply (f : X → Measure Y) (hf : Measurable f) (μ : Measure X) (A : Set Y)
    (hA : MeasurableSet A) :
    Measure.bind f μ A = ∫⁻ x, f x A ∂μ := by
  rw [Measure.bind, dif_pos hf]
  apply Measure.ofMeasurable_apply _ hA

theorem Measure.dirac_lintegral (f : X → ℝ≥0∞) (hf : Measurable f) (x : X) :
    ∫⁻ y, f y ∂(Measure.dirac x) = f x := by
  have : f =ᶠ[ae (Measure.dirac x)] Function.const X (f x) := by
    have : ∀ᵐ y ∂(Measure.dirac x), y ∈ { y | f y = f x } := by
      rw [eventually_mem_set, mem_ae_iff, dirac_apply]
      · simp
      · apply MeasurableSet.compl
        suffices MeasurableSet (f ⁻¹' {f x}) from this
        apply hf (MeasurableSet.singleton (f x))
    filter_upwards [this] with y hy using by simpa using hy
  apply (lintegral_congr_ae this).trans (by simp)

theorem Measure.dirac_bind (f : X → Measure Y) (hf : Measurable f) (x : X) :
    Measure.bind f (Measure.dirac x) = f x := by
  ext A hA
  simp only [Measure.bind_apply f hf (Measure.dirac x) A hA]
  rw [Measure.dirac_lintegral (fun y => f y A) ((Measure.measurable_coe hA).comp hf) x]

theorem Measure.bind_dirac (μ : Measure X) :
    Measure.bind Measure.dirac μ = μ := by
  ext A hA
  simp only [Measure.bind_apply Measure.dirac Measure.dirac_measurable μ A hA]
  simp only [Measure.dirac_apply _ A hA]
  rw [lintegral_indicator hA fun x ↦ 1]
  rw [@setLIntegral_one]

theorem lintegral_bind {m : Measure X} {μ : X → Measure Y} {f : Y → ℝ≥0∞} (hμ : Measurable μ)
    (hf : Measurable f) : ∫⁻ y, f y ∂Measure.bind μ m = ∫⁻ x, ∫⁻ y, f y ∂μ x ∂m := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  dsimp only [SimpleFunc.lintegral]
  calc
    ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        a * (Measure.bind μ m) ((SimpleFunc.eapprox f n) ⁻¹' {a})
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        a * (∫⁻ x, μ x ((SimpleFunc.eapprox f n) ⁻¹' {a}) ∂m) := by
      congr 1
      ext n
      congr 1
      ext a
      congr 1
      rw [Measure.bind_apply μ hμ m]
      exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox f n) a
    _ = ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        (∫⁻ x, a * μ x ((SimpleFunc.eapprox f n) ⁻¹' {a}) ∂m) := by
      congr 1
      ext n
      congr 1
      ext a
      apply (lintegral_const_mul _ _).symm
      have : (fun x ↦ (μ x) ((SimpleFunc.eapprox f n) ⁻¹' {a})) =
          ((fun ν : Measure Y ↦ ν ((SimpleFunc.eapprox f n) ⁻¹' {a})) ∘ μ) := by
        rfl
      rw [this]
      apply Measurable.comp _ hμ
      refine Measure.measurable_coe ?_
      exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox f n) a
    _ = ⨆ n, (∫⁻ x, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        a * μ x ((SimpleFunc.eapprox f n) ⁻¹' {a}) ∂m) := by
      congr 1
      ext n
      refine Eq.symm (lintegral_finset_sum' (SimpleFunc.eapprox f n).range ?_)
      intro a ha
      apply Measurable.aemeasurable
      refine Measurable.mul ?_ ?_
      · exact measurable_const
      · have : (fun x ↦ (μ x) ((SimpleFunc.eapprox f n) ⁻¹' {a})) =
            ((fun ν : Measure Y ↦ ν ((SimpleFunc.eapprox f n) ⁻¹' {a})) ∘ μ) := by
          rfl
        rw [this]
        apply Measurable.comp _ hμ
        refine Measure.measurable_coe ?_
        exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox f n) a
    _ = (∫⁻ x, ⨆ n, ∑ a ∈ (SimpleFunc.eapprox f n).range,
        a * μ x ((SimpleFunc.eapprox f n) ⁻¹' {a}) ∂m) := by
      refine Eq.symm (lintegral_iSup' ?_ ?_)
      · intro n
        apply Measurable.aemeasurable
        refine Finset.measurable_fun_sum (SimpleFunc.eapprox f n).range ?_
        intro a ha
        refine Measurable.const_mul ?_ a
        have : (fun x ↦ (μ x) ((SimpleFunc.eapprox f n) ⁻¹' {a})) =
            ((fun ν : Measure Y ↦ ν ((SimpleFunc.eapprox f n) ⁻¹' {a})) ∘ μ) := by
          rfl
        rw [this]
        apply Measurable.comp _ hμ
        refine Measure.measurable_coe ?_
        exact SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox f n) a
      · filter_upwards with a i j hij
        simp only
        rw [← SimpleFunc.lintegral]
        rw [← SimpleFunc.lintegral]
        apply SimpleFunc.lintegral_mono _ (le_of_eq rfl)
        apply SimpleFunc.monotone_eapprox f hij
    _ = ∫⁻ (a : X), ∫⁻ (x : Y), f x ∂μ a ∂m := by
      apply lintegral_congr
      intro x
      simp only [← SimpleFunc.iSup_eapprox_apply hf]
      rw [lintegral_iSup]
      · congr 1
        ext n
        rw [SimpleFunc.lintegral_eq_lintegral]
        rw [SimpleFunc.lintegral]
      · intro n
        exact SimpleFunc.measurable (SimpleFunc.eapprox f n)
      · intro i j hij
        dsimp only
        gcongr
  -- simp only [Measure.bind_apply μ hμ m ((SimpleFunc.eapprox f n) ⁻¹' {_}) _]
  -- sorry
  -- (lintegral_join hf).trans (lintegral_map' (aemeasurable_lintegral hf) hμ)

theorem Measure.bind_measurable (f : X → Measure Y) (hf : Measurable f) :
    Measurable (Measure.bind f) := by
  refine measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp only [Measure.bind_apply f hf _ A hA]
  apply measurable_lintegral
  exact (Measure.measurable_coe hA).comp hf

theorem Measure.bind_assoc
    (ν : X → Measure Y) (hν : Measurable ν)
    (ℓ : Y → Measure Z) (hℓ : Measurable ℓ)
    (μ : Measure X) :
    Measure.bind ℓ (Measure.bind ν μ) =
      Measure.bind (Measure.bind ℓ ∘ ν) μ := by
  ext C hC
  rw [Measure.bind_apply ℓ hℓ (Measure.bind ν μ) C hC]
  rw [Measure.bind_apply _ ((bind_measurable ℓ hℓ).comp hν) _ _ hC]
  rw [lintegral_bind hν]
  · apply lintegral_congr (fun x ↦ (Measure.bind_apply ℓ hℓ (ν x) C hC).symm)
  · apply (measurable_coe hC).comp hℓ

def sum {ι : Type*} (f : ι → Measure X) : Measure X :=
  (OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure <|
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)

def Measure.sum' {I : Type*} (μ : I → Measure X) : Measure X :=
  Measure.ofMeasurable (fun A _ => ∑' i, μ i A) (by simp)  <| fun A hA hAd => by
    dsimp only
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro i
    rw [measure_iUnion hAd hA]

theorem Measure.sum'_apply {I : Type*} (μ : I → Measure X) {A : Set X} (hA : MeasurableSet A) :
    Measure.sum' μ A = ∑' i, μ i A := by
  rw [Measure.sum']
  rw [Measure.ofMeasurable_apply _ hA]

theorem SimpleFunc.lintegral_sum'_measure {I : Type*} {μ : I → Measure X} {f : SimpleFunc X ℝ≥0∞} :
    f.lintegral (Measure.sum' μ) = ∑' i, f.lintegral (μ i) := by
  -- simp_rw [Measure.sum']
  simp_rw [SimpleFunc.lintegral]
  simp_rw [Measure.sum'_apply _ (SimpleFunc.measurableSet_fiber f _)]
  simp_rw [← ENNReal.tsum_mul_left]
  refine Eq.symm (Summable.tsum_finsetSum ?_)
  intro y hy
  simp only [ENNReal.summable]


theorem lintegral_measure_add'' (μ ν : Measure X) {f : X → ℝ≥0∞} :
    ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν := by
  simp_rw [lintegral_def]
  set S := { i : SimpleFunc X ℝ≥0∞ // i ≤ fun a ↦ f a }
  simp_rw [iSup_subtype']
  have : ∀ g : SimpleFunc X ℝ≥0∞, g.lintegral μ + g.lintegral ν = g.lintegral (μ + ν) := by
    intro g
    simp_rw [SimpleFunc.lintegral]
    simp only [Measure.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have : ⨆ g : S, SimpleFunc.lintegral g (μ + ν) =
      (⨆ g : S, SimpleFunc.lintegral g μ + SimpleFunc.lintegral g ν) := by
      exact Eq.symm (iSup_congr fun i ↦ this i)
  rw [this]
  -- simp_rw [SimpleFunc.lintegral_add]
  have : IsDirectedOrder S := by
    constructor
    rintro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩
    refine ⟨⟨g₁ ⊔ g₂, ?_⟩, ⟨?_, ?_⟩⟩
    · intro a
      simp only [SimpleFunc.coe_sup, Pi.sup_apply, sup_le_iff]
      exact ⟨hg₁ a, hg₂ a⟩
    · intro x
      simp
    · intro x
      simp
  rw [iSup_add_iSup_of_monotone]
  all_goals
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ hgg'
    simp only [Subtype.mk_le_mk] at hgg'
    apply SimpleFunc.lintegral_mono hgg' (le_of_eq rfl)

theorem lintegral_finset_sum'_measure (f : X → ℝ≥0∞) (μ : ℕ → Measure X) (n : ℕ) :
    ∫⁻ (a : X), f a ∂∑ i ∈ Finset.range n, μ i = ∑ i ∈ Finset.range n, ∫⁻ (a : X), f a ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ∑ i ∈ Finset.range (n + 1), μ i = ∑ i ∈ Finset.range n, μ i + μ n := by
      simp only [Finset.sum_range_succ]
    rw [this]
    rw [@lintegral_measure_add'']
    rw [ih]
    rw [@Finset.sum_range_succ]

set_option linter.unusedDecidableInType false in
theorem lintegral_finset_sum''_measure {I : Type*} [DecidableEq I]
    (J : Finset I) (f : X → ℝ≥0∞) (μ : I → Measure X) :
    ∫⁻ (a : X), f a ∂∑ i ∈ J, μ i = ∑ i ∈ J, ∫⁻ (a : X), f a ∂μ i := by
  induction J using Finset.induction with
  | empty => simp
  | insert i J' hi ih =>
    rw [Finset.sum_insert hi]
    rw [@lintegral_measure_add'']
    rw [ih]
    rw [Finset.sum_insert hi]

theorem SimpleFunc.lintegral_finset_sum (f : SimpleFunc X ℝ≥0∞) (μ : ℕ → Measure X) (n : ℕ) :
    f.lintegral (∑ i ∈ Finset.range n, μ i) = ∑ i ∈ Finset.range n, f.lintegral (μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [SimpleFunc.lintegral]
    have : ∑ i ∈ Finset.range (n + 1), μ i = ∑ i ∈ Finset.range n, μ i + μ n := by
      simp only [Finset.sum_range_succ]
    rw [this]
    rw [SimpleFunc.lintegral] at ih
    rw [Finset.sum_range_succ]
    simp only [Measure.coe_add, Measure.coe_finset_sum, Pi.add_apply, Finset.sum_apply]
    simp only [Measure.coe_finset_sum, Finset.sum_apply] at ih
    -- rw [@Finset.sum_comm]
    simp_rw [mul_add]
    rw [@Finset.sum_add_distrib]
    rw [ih]
    rw [← SimpleFunc.lintegral]
    rfl

set_option linter.unusedDecidableInType false in
theorem SimpleFunc.lintegral_finset_sum' {I : Type*} [DecidableEq I] (J : Finset I)
    (f : SimpleFunc X ℝ≥0∞) (μ : I → Measure X) :
    f.lintegral (∑ i ∈ J, μ i) = ∑ i ∈ J, f.lintegral (μ i) := by
  induction J using Finset.induction with
  | empty => simp
  | insert i J' hi ih =>
    simp_rw [SimpleFunc.lintegral]
    rw [Finset.sum_insert hi]
    rw [SimpleFunc.lintegral] at ih
    rw [Finset.sum_insert hi]
    simp only [Measure.coe_add, Measure.coe_finset_sum, Pi.add_apply, Finset.sum_apply]
    simp only [Measure.coe_finset_sum, Finset.sum_apply] at ih
    simp_rw [mul_add]
    rw [@Finset.sum_add_distrib]
    rw [ih]
    rw [← SimpleFunc.lintegral]
    rfl

theorem lintegral_sum'_measure {μ : ℕ → Measure X} {f : X → ℝ≥0∞} :
    ∫⁻ a, f a ∂Measure.sum' μ = ∑' i, ∫⁻ a, f a ∂μ i := by
  -- simp_rw [lintegral_eq_iSup_eapprox_lintegral hf]
  rw [@ENNReal.tsum_eq_iSup_nat]
  simp_rw [← lintegral_finset_sum'_measure,
    lintegral, SimpleFunc.lintegral_sum'_measure,
    SimpleFunc.lintegral_finset_sum]
  rw [iSup_comm]
  apply iSup_congr
  intro g
  conv_rhs => rw [iSup_comm]
  apply iSup_congr
  intro hg
  rw [@ENNReal.tsum_eq_iSup_nat]

theorem lintegral_sum''_measure {I : Type*} {μ : I → Measure X} {f : X → ℝ≥0∞} :
    ∫⁻ a, f a ∂Measure.sum' μ = ∑' i, ∫⁻ a, f a ∂μ i := by
  -- simp_rw [lintegral_eq_iSup_eapprox_lintegral hf]
  rw [@ENNReal.tsum_eq_iSup_sum]
  classical
  simp_rw [← lintegral_finset_sum''_measure, lintegral]
  conv_rhs => rw [iSup_comm]
  conv_rhs =>
    congr
    ext g
    rw [iSup_comm]
  apply iSup_congr
  intro g
  apply iSup_congr
  intro hg
  simp_rw [SimpleFunc.lintegral_finset_sum']
  rw [@SimpleFunc.lintegral_sum'_measure]
  rw [@ENNReal.tsum_eq_iSup_sum]

open Function in
theorem restrict_iUnion {I : Type*} [Countable I] {μ : Measure X} {A : I → Set X}
    (hd : Pairwise (Disjoint on A)) (hm : ∀ i, MeasurableSet (A i)) :
    μ.restrict (⋃ i, A i) = Measure.sum' fun i => μ.restrict (A i) := by
  ext B hB
  rw [Measure.sum'_apply _ hB]
  simp only [Measure.restrict_apply hB]
  rw [@inter_iUnion]
  rw [measure_iUnion]
  · intro i j hij C hCi hCj x hx
    have hCi' : C ⊆ A i := (subset_inter_iff.mp hCi).2
    have hCj' : C ⊆ A j := (subset_inter_iff.mp hCj).2
    apply hd hij hCi' hCj' hx
  · intro i
    apply hB.inter (hm i)

open Function in
theorem lintegral_iUnion {μ : Measure X} {A : ℕ → Set X} (hm : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) (f : X → ℝ≥0∞) :
    ∫⁻ a in ⋃ i, A i, f a ∂μ = ∑' i, ∫⁻ a in A i, f a ∂μ := by
  rw [restrict_iUnion hd hm]
  rw [@lintegral_sum'_measure]


def Measure.withDensity (μ : Measure X) (f : X → ℝ≥0∞) : Measure X :=
  Measure.ofMeasurable (fun s _ => ∫⁻ a in s, f a ∂μ) (by simp) fun _ hs hd =>
    lintegral_iUnion hs hd _

@[simp]
theorem withDensity_apply (μ : Measure X) (f : X → ℝ≥0∞) {s : Set X} (hs : MeasurableSet s) :
    Measure.withDensity μ f s = ∫⁻ a in s, f a ∂μ :=
  Measure.ofMeasurable_apply s hs

example (μ ν : Measure X) : Measure X := by
  apply Measure.ofMeasurable (fun s _ => μ s + ν s) (by simp) <| by
    intro f hf h
    dsimp only
    rw [measure_iUnion h hf]
    rw [measure_iUnion h hf]
    rw [← @ENNReal.tsum_add]

example : ContinuousAdd ℝ≥0∞ := by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · dsimp only [none_eq_top]
    exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  simp only [ContinuousAt, some_eq_coe, nhds_coe_coe, ← coe_add, tendsto_map'_iff,
    Function.comp_def, tendsto_coe, tendsto_add]

theorem lintegral_measure_add (μ ν : Measure X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν := by
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hf]
  rw [iSup_add_iSup_of_monotone]
  · apply iSup_congr
    intro n
    simp_rw [SimpleFunc.lintegral]
    simp only [Measure.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  all_goals
    intro i j hij
    apply SimpleFunc.lintegral_mono _ (le_of_eq rfl)
    apply SimpleFunc.monotone_eapprox _ hij

theorem lintegral_measure_add' (μ ν : Measure X) {f : X → ℝ≥0∞} :
    ∫⁻ a, f a ∂(μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν := by
  simp_rw [lintegral_def]
  simp_rw [iSup_subtype']
  simp_rw [SimpleFunc.lintegral_add]
  apply le_antisymm
  · apply iSup_le
    intro g
    apply add_le_add
    · apply le_iSup_of_le g (le_of_eq rfl)
    · apply le_iSup_of_le g (le_of_eq rfl)
  · let S := { i : SimpleFunc X ℝ≥0∞ // ⇑i ≤ fun a ↦ f a }
    have : Nonempty S := by
      apply Nonempty.intro
      refine ⟨SimpleFunc.const X 0, ?_⟩
      simp
    have :  (⨆ g₁ : S, SimpleFunc.lintegral g₁ μ) + ⨆ g₂ : S, SimpleFunc.lintegral g₂ ν
        = ⨆ g₁ : S, SimpleFunc.lintegral g₁ μ + ⨆ g₂ : S, SimpleFunc.lintegral g₂ ν := by
      set a := ⨆ g₂ : S, SimpleFunc.lintegral g₂ ν
      obtain ha | ha := eq_or_ne a ∞
      · simp [ha]
      apply le_antisymm
      · apply add_le_of_le_tsub_right_of_le
        · apply le_iSup_of_le ⟨SimpleFunc.const X 0, by simp⟩
          simp
        · apply iSup_le
          intro g₁
          apply ENNReal.le_sub_of_add_le_left ha
          rw [add_comm]
          exact le_iSup_iff.mpr fun b a ↦ a g₁
      · simp only [iSup_le_iff]
        rintro ⟨g, hg⟩
        apply add_le_add
        · exact le_iSup_iff.mpr fun b a ↦ a ⟨g, hg⟩
        · apply le_of_eq rfl
    rw [this]
    apply iSup_le
    rintro ⟨g₁, hg₁⟩
    simp only
    have : g₁.lintegral μ + ⨆ g₂ : S, SimpleFunc.lintegral g₂ ν =
        ⨆ g₂ : S, g₁.lintegral μ + SimpleFunc.lintegral g₂ ν := by
      rw [@add_iSup]
    rw [this]
    apply iSup_le
    rintro ⟨g₂, hg₂⟩
    dsimp only
    refine le_iSup_of_le ⟨g₁ ⊔ g₂, ?_⟩ ?_
    · intro a
      simp only [SimpleFunc.coe_sup, Pi.sup_apply, sup_le_iff]
      exact ⟨hg₁ a, hg₂ a⟩
    · simp only
      apply add_le_add
      · apply SimpleFunc.lintegral_mono (le_sup_left) (le_of_eq rfl)
      · apply SimpleFunc.lintegral_mono (le_sup_right) (le_of_eq rfl)



theorem lintegral_withDensity_eq_lintegral_mul (μ : Measure X) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, g a ∂(Measure.withDensity μ f) = ∫⁻ a, (f * g) a ∂μ := by
  have lhs := calc
    ∫⁻ a, g a ∂(Measure.withDensity μ f) =
      ∫⁻ (a : X), ⨆ i, (SimpleFunc.eapprox g i) a ∂Measure.withDensity μ f :=
        lintegral_congr fun x ↦ (SimpleFunc.iSup_eapprox_apply hg x).symm
    _ = ⨆ n, ∫⁻ (a : X), (SimpleFunc.eapprox g n) a ∂Measure.withDensity μ f :=
        lintegral_iSup (fun n ↦ (SimpleFunc.eapprox g n).measurable) (SimpleFunc.monotone_eapprox g)
  have rhs := calc
    ∫⁻ a, (f * g) a ∂μ =
      ∫⁻ (a : X), ⨆ i, f a * (SimpleFunc.eapprox g i) a ∂μ := by
        apply lintegral_congr
        intro a
        simp only [Pi.mul_apply, ← mul_iSup]
        apply congrArg _ (SimpleFunc.iSup_eapprox_apply hg a).symm
    _ = ⨆ n, ∫⁻ (a : X), f a * (SimpleFunc.eapprox g n) a ∂μ := by
        apply lintegral_iSup
        · intro n
          apply hf.mul (SimpleFunc.eapprox g n).measurable
        · apply (monotone_lam fun x ↦ Monotone.const_mul'
            (fun a b hab ↦ SimpleFunc.monotone_eapprox g hab x) (f x))
  rw [lhs, rhs]
  apply iSup_congr
  intro n
  calc
    ∫⁻ (a : X), (SimpleFunc.eapprox g n) a ∂Measure.withDensity μ f
    _ =  ∑ x ∈ (SimpleFunc.eapprox g n).range,
            ∫⁻ (a : X) in (SimpleFunc.eapprox g n) ⁻¹' {x}, x * f a ∂μ := by
      rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
      apply Finset.sum_congr rfl
      intro a ha
      rw [withDensity_apply _ _ ((SimpleFunc.eapprox g n).measurableSet_fiber a)]
      rw [lintegral_const_mul _ hf]
    _ = ∑ x ∈ (SimpleFunc.eapprox g n).range,
      ∫⁻ (a : X) in (SimpleFunc.eapprox g n) ⁻¹' {x}, (SimpleFunc.eapprox g n) a * f a ∂μ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply setLIntegral_congr_fun ((SimpleFunc.eapprox g n).measurableSet_fiber x)
      intro x' hx'
      simp only [mem_preimage, mem_singleton_iff] at hx'
      dsimp only
      rw [hx']
    _ = ∫⁻ (a : X), f a * (SimpleFunc.eapprox g n) a ∂μ := by
      rw [← lintegral_finset_sum_measure]
      apply congrArg₂
      · ext A hA
        simp only [Measure.coe_finset_sum, Finset.sum_apply]
        simp only [Measure.restrict_apply hA]
        rw [← measure_biUnion_finset]
        · apply congrArg
          ext a
          simp only [← inter_iUnion]
          rw [@mem_inter_iff]
          simp
        · have : ((SimpleFunc.eapprox g n).range : Set ℝ≥0∞).PairwiseDisjoint
              fun x ↦ (SimpleFunc.eapprox g n) ⁻¹' {x} := by
            exact pairwiseDisjoint_fiber (SimpleFunc.eapprox g n) (SimpleFunc.eapprox g n).range
          intro a ha b hb hab s ha' hb'
          simp only [le_eq_subset, subset_inter_iff] at ha' hb'
          apply this ha hb hab ha'.2 hb'.2
        · intro b hb
          exact hA.inter ((SimpleFunc.eapprox g n).measurableSet_fiber b)
      · ext a
        ring

theorem lintegral_withDensity_eq_lintegral_mul' (μ : Measure X) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, g a ∂(Measure.withDensity μ f) = ∫⁻ a, (f * g) a ∂μ := by
  rw [← SimpleFunc.iSup_coe_eapprox hg]
  simp only [iSup_apply, Pi.mul_apply]
  rw [lintegral_iSup (fun n ↦ (SimpleFunc.eapprox g n).measurable) (SimpleFunc.monotone_eapprox g)]
  simp only [mul_iSup]
  rw [lintegral_iSup
    (fun n ↦ hf.mul (SimpleFunc.eapprox g n).measurable)
    (monotone_lam fun x ↦ Monotone.const_mul'
      (fun a b hab ↦ SimpleFunc.monotone_eapprox g hab x) (f x))]
  apply iSup_congr
  intro n
  rw [SimpleFunc.lintegral_eq_lintegral, SimpleFunc.lintegral]
  have : ∀ x, MeasurableSet (((SimpleFunc.eapprox g n) ⁻¹' {x})) := by
    intro x
    apply SimpleFunc.measurableSet_fiber (SimpleFunc.eapprox g n) x
  simp only [withDensity_apply μ f (this _)]
  simp only [← lintegral_const_mul _ hf]
  calc
    ∑ x ∈ (SimpleFunc.eapprox g n).range,
      ∫⁻ (a : X) in (SimpleFunc.eapprox g n) ⁻¹' {x}, x * f a ∂μ =
    ∑ x ∈ (SimpleFunc.eapprox g n).range,
      ∫⁻ (a : X) in (SimpleFunc.eapprox g n) ⁻¹' {x}, (SimpleFunc.eapprox g n) a * f a ∂μ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply setLIntegral_congr_fun ((SimpleFunc.eapprox g n).measurableSet_fiber x)
      intro x' hx'
      simp only [mem_preimage, mem_singleton_iff] at hx'
      dsimp only
      rw [hx']
    _ = ∫⁻ (a : X), f a * (SimpleFunc.eapprox g n) a ∂μ := by
      rw [← lintegral_finset_sum_measure]
      congr 1
      · ext A hA
        simp only [Measure.coe_finset_sum, Finset.sum_apply]
        simp only [Measure.restrict_apply hA]
        rw [← measure_biUnion_finset]
        · congr 1
          ext a
          simp
        · have : ((SimpleFunc.eapprox g n).range : Set ℝ≥0∞).PairwiseDisjoint
              fun x ↦ (SimpleFunc.eapprox g n) ⁻¹' {x} := by
            exact pairwiseDisjoint_fiber ⇑(SimpleFunc.eapprox g n) ↑(SimpleFunc.eapprox g n).range
          intro a ha b hb hab s ha' hb'
          simp only [le_eq_subset, subset_inter_iff] at ha' hb'
          apply this ha hb hab ha'.2 hb'.2
        · intro b hb
          exact MeasurableSet.inter hA (this b)
      · ext a
        ring

def Measure.count' : Measure X :=
  Measure.ofMeasurable (fun A _ ↦ A.encard) (by simp) fun A hA hAd => by
    dsimp only
    simp_rw [← ENat.card_coe_set_eq]
    rw [← ENNReal.tsum_one]
    have : ∀ i : ℕ, ENat.card ↑(A i) = ∑' (x : A i), (1 : ℝ≥0∞) := by
      intro i
      exact Eq.symm tsum_one
    simp_rw [this _]
    rw [ENNReal.tsum_biUnion (f := fun x ↦ 1)]
    intro i _ j _ hij
    apply hAd hij

end Playground


namespace MeasureTheory

namespace Measure




variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Measurability structure on `Measure`: Measures are measurable w.r.t. all projections -/
instance instMeasurableSpace : MeasurableSpace (Measure α) :=
  ⨆ (s : Set α) (_ : MeasurableSet s), (borel ℝ≥0∞).comap fun μ => μ s

theorem measurable_coe {s : Set α} (hs : MeasurableSet s) : Measurable fun μ : Measure α => μ s :=
  Measurable.of_comap_le <| le_iSup_of_le s <| le_iSup_of_le hs <| le_rfl

theorem measurable_of_measurable_coe (f : β → Measure α)
    (h : ∀ (s : Set α), MeasurableSet s → Measurable fun b => f b s) : Measurable f :=
  Measurable.of_le_map <|
    iSup₂_le fun s hs =>
      MeasurableSpace.comap_le_iff_le_map.2 <| by rw [MeasurableSpace.map_comp]; exact h s hs

instance instMeasurableAdd₂ {α : Type*} {m : MeasurableSpace α} : MeasurableAdd₂ (Measure α) := by
  refine ⟨Measure.measurable_of_measurable_coe _ fun s hs => ?_⟩
  simp_rw [Measure.coe_add, Pi.add_apply]
  refine Measurable.add ?_ ?_
  · exact (Measure.measurable_coe hs).comp measurable_fst
  · exact (Measure.measurable_coe hs).comp measurable_snd

-- There is no typeclass for measurability of `SMul` only on that side, otherwise we could
-- turn that into an instance.
@[fun_prop]
lemma _root_.Measurable.smul_measure {f : α → ℝ≥0∞} (hf : Measurable f) (μ : Measure β) :
    Measurable (fun x ↦ f x • μ) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  fun_prop

theorem measurable_measure {μ : α → Measure β} :
    Measurable μ ↔ ∀ (s : Set β), MeasurableSet s → Measurable fun b => μ b s :=
  ⟨fun hμ _s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

@[fun_prop]
theorem measurable_map (f : α → β) (hf : Measurable f) :
    Measurable fun μ : Measure α => map f μ := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [map_apply hf hs]
  exact measurable_coe (hf hs)

@[fun_prop]
theorem measurable_dirac : Measurable (Measure.dirac : α → Measure α) := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [dirac_apply' _ hs]
  exact measurable_one.indicator hs

@[fun_prop]
theorem measurable_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n => Finset.measurable_fun_sum _ fun i _ => ?_
  refine Measurable.const_mul ?_ _
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)

end Measure

end MeasureTheory
