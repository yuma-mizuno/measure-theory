import Mathlib.Algebra.Algebra.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Simple functions
-/

noncomputable section

open Set hiding restrict restrict_apply
open Filter ENNReal
open Function (support)
open Topology NNReal ENNReal MeasureTheory

namespace MTI

/-- A simple function is an `ℝ≥0∞`-valued measurable function with finite range. -/
structure SimpleFunc (X : Type*) [MeasurableSpace X] where
  /-- The underlying function. -/
  toFun : X → ℝ≥0∞
  measurableSet_fiber' : ∀ x, MeasurableSet (toFun ⁻¹' {x})
  finite_range' : (Set.range toFun).Finite

namespace SimpleFunc

section Measurable

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

instance instFunLike : FunLike (SimpleFunc X) X ℝ≥0∞ where
  coe := SimpleFunc.toFun
  coe_injective' | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

theorem coe_injective ⦃f g : SimpleFunc X⦄ (h : (f : X → ℝ≥0∞) = g) : f = g :=
  DFunLike.ext' h

@[ext]
theorem ext {f g : SimpleFunc X} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

theorem finite_range (f : SimpleFunc X) : (Set.range f).Finite :=
  f.finite_range'

theorem measurableSet_fiber (f : SimpleFunc X) (x : ℝ≥0∞) : MeasurableSet (f ⁻¹' {x}) :=
  f.measurableSet_fiber' x

@[simp] theorem coe_mk (f : X → ℝ≥0∞) (h h') : ⇑(SimpleFunc.mk f h h') = f := rfl

theorem apply_mk (f : X → ℝ≥0∞) (h h') (x : X) : SimpleFunc.mk f h h' x = f x := rfl

/-- Range as a finset. -/
protected def range (f : SimpleFunc X) : Finset ℝ≥0∞ :=
  f.finite_range.toFinset

@[simp]
theorem mem_range {f : SimpleFunc X} {x : ℝ≥0∞} : x ∈ f.range ↔ x ∈ Set.range f :=
  Finite.mem_toFinset _

theorem mem_range_self (f : SimpleFunc X) (x : X) : f x ∈ f.range :=
  mem_range.2 ⟨x, rfl⟩

@[simp]
theorem coe_range (f : SimpleFunc X) : (↑f.range : Set ℝ≥0∞) = Set.range f :=
  f.finite_range.coe_toFinset

theorem mem_range_of_measure_ne_zero {f : SimpleFunc X} {x : ℝ≥0∞} {μ : Measure X}
    (h : μ (f ⁻¹' {x}) ≠ 0) : x ∈ f.range := by
  let ⟨a, ha⟩ := nonempty_of_measure_ne_zero h
  exact mem_range.2 ⟨a, ha⟩

theorem forall_mem_range {f : SimpleFunc X} {p : ℝ≥0∞ → Prop} :
    (∀ y ∈ f.range, p y) ↔ ∀ x, p (f x) := by
  simp only [mem_range, Set.forall_mem_range]

theorem preimage_eq_empty_iff (f : SimpleFunc X) (x : ℝ≥0∞) :
    f ⁻¹' {x} = ∅ ↔ x ∉ f.range :=
  preimage_singleton_eq_empty.trans <| not_congr mem_range.symm

/-- Constant simple function. -/
def const (X : Type*) [MeasurableSpace X] (c : ℝ≥0∞) : SimpleFunc X :=
  ⟨fun _ ↦ c, fun _ ↦ MeasurableSet.const _, finite_range_const⟩

instance : Inhabited (SimpleFunc X) := ⟨const X 0⟩

theorem const_apply (x : X) (c : ℝ≥0∞) : const X c x = c := rfl

@[simp]
theorem coe_const (c : ℝ≥0∞) : ⇑(const X c) = Function.const X c := rfl

@[simp]
theorem range_const (X : Type*) [MeasurableSpace X] [Nonempty X] (c : ℝ≥0∞) :
    (const X c).range = {c} :=
  Finset.coe_injective <| by simp +unfoldPartialApp [Function.const]

theorem measurableSet_cut (r : X → ℝ≥0∞ → Prop) (f : SimpleFunc X)
    (h : ∀ y, MeasurableSet {x | r x y}) : MeasurableSet {x | r x (f x)} := by
  have h_union : {x | r x (f x)} = ⋃ y ∈ Set.range f, {x | r x y} ∩ f ⁻¹' {y} := by
    ext x
    suffices r x (f x) ↔ ∃ i, r x (f i) ∧ f x = f i by simpa
    exact ⟨fun hx ↦ ⟨x, ⟨hx, rfl⟩⟩, fun ⟨i, hi⟩ ↦ hi.2.symm ▸ hi.1⟩
  rw [h_union]
  exact MeasurableSet.biUnion f.finite_range.countable fun y _ ↦
    MeasurableSet.inter (h y) (f.measurableSet_fiber y)

@[measurability]
theorem measurableSet_preimage (f : SimpleFunc X) (s : Set ℝ≥0∞) :
    MeasurableSet (f ⁻¹' s) :=
  measurableSet_cut (fun _ y ↦ y ∈ s) f fun y ↦ MeasurableSet.const (y ∈ s)

@[fun_prop]
protected theorem measurable (f : SimpleFunc X) :
    Measurable f := fun s _ ↦
  f.measurableSet_preimage s

protected theorem sum_measure_preimage_singleton (f : SimpleFunc X) {μ : Measure X}
    (s : Finset ℝ≥0∞) : (∑ y ∈ s, μ (f ⁻¹' {y})) = μ (f ⁻¹' ↑s) :=
  sum_measure_preimage_singleton _ fun _ _ ↦ f.measurableSet_fiber _

theorem sum_range_measure_preimage_singleton (f : SimpleFunc X) (μ : Measure X) :
    (∑ y ∈ f.range, μ (f ⁻¹' {y})) = μ univ := by
  rw [f.sum_measure_preimage_singleton, coe_range, preimage_range]

open scoped Classical in
/-- Piecewise combination of simple functions. -/
def piecewise (s : Set X) (hs : MeasurableSet s) (f g : SimpleFunc X) : SimpleFunc X :=
  ⟨s.piecewise f g, fun y ↦
    f.measurable.piecewise hs g.measurable (measurableSet_singleton y),
   (f.finite_range.union g.finite_range).subset range_ite_subset⟩

open scoped Classical in
@[simp]
theorem coe_piecewise {s : Set X} (hs : MeasurableSet s) (f g : SimpleFunc X) :
    ⇑(piecewise s hs f g) = s.piecewise f g := rfl

open scoped Classical in
theorem piecewise_apply {s : Set X} (hs : MeasurableSet s) (f g : SimpleFunc X) (x : X) :
    piecewise s hs f g x = if x ∈ s then f x else g x := rfl

@[simp]
theorem piecewise_univ (f g : SimpleFunc X) :
    piecewise univ MeasurableSet.univ f g = f := by
  ext x
  simp [piecewise_apply]

@[simp]
theorem piecewise_empty (f g : SimpleFunc X) :
    piecewise ∅ MeasurableSet.empty f g = g := by
  ext x
  simp [piecewise_apply]

/-- Pointwise endomorphism of simple functions. -/
def map (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc X) : SimpleFunc X where
  toFun := g ∘ f
  measurableSet_fiber' y := f.measurableSet_preimage {x | g x = y}
  finite_range' := by
    refine (f.range.image g).finite_toSet.subset ?_
    apply subset_of_eq
    rw [@Finset.coe_image]
    rw [@coe_range]
    rw [@range_comp]

@[simp]
theorem map_apply (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc X) (x : X) : f.map g x = g (f x) := rfl

@[simp]
theorem coe_map (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc X) : (f.map g : X → ℝ≥0∞) = g ∘ f := rfl

@[simp]
theorem range_map (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc X) : (f.map g).range = f.range.image g :=
  Finset.coe_injective <| by simp only [coe_range, coe_map, Finset.coe_image, range_comp]

open scoped Classical in
theorem map_preimage_singleton (f : SimpleFunc X) (g : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0∞) :
    f.map g ⁻¹' {c} = f ⁻¹' ↑{b ∈ f.range | g b = c} := by
  ext x
  simp

/-- Pointwise binary operation on simple functions. -/
def map₂ (f g : SimpleFunc X) (op : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : SimpleFunc X where
  toFun := fun x ↦ op (f x) (g x)
  measurableSet_fiber' c :=
    f.measurableSet_cut (fun x a ↦ op a (g x) = c) fun a ↦
      g.measurableSet_preimage {b | op a b = c}
  finite_range' :=
    ((f.range.product g.range).image fun p : ℝ≥0∞ × ℝ≥0∞ ↦ op p.1 p.2).finite_toSet.subset <| by
      rintro _ ⟨x, rfl⟩
      simp

theorem map₂_apply (f g : SimpleFunc X) (op : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (x : X) :
    f.map₂ g op x = op (f x) (g x) := rfl

/-- Composition with a measurable function. -/
def comp (f : SimpleFunc Y) (g : X → Y) (hg : Measurable g) : SimpleFunc X where
  toFun := f ∘ g
  measurableSet_fiber' y := hg (f.measurableSet_fiber y)
  finite_range' := f.finite_range.subset <| Set.range_comp_subset_range _ _

@[simp]
theorem coe_comp (f : SimpleFunc Y) {g : X → Y} (hg : Measurable g) :
    ⇑(f.comp g hg) = f ∘ g := rfl

instance : Zero (SimpleFunc X) := ⟨const X 0⟩
instance : Add (SimpleFunc X) := ⟨fun f g ↦ f.map₂ g (· + ·)⟩
instance : Mul (SimpleFunc X) := ⟨fun f g ↦ f.map₂ g (· * ·)⟩
instance : Max (SimpleFunc X) := ⟨fun f g ↦ f.map₂ g max⟩
instance : LE (SimpleFunc X) := ⟨fun f g ↦ ∀ x, f x ≤ g x⟩

@[simp, norm_cast] theorem coe_zero : ⇑(0 : SimpleFunc X) = (0 : X → ℝ≥0∞) := rfl
@[simp, norm_cast] theorem coe_add (f g : SimpleFunc X) : ⇑(f + g) = ⇑f + ⇑g := rfl
@[simp, norm_cast] theorem coe_mul (f g : SimpleFunc X) : ⇑(f * g) = ⇑f * ⇑g := rfl
@[simp, norm_cast] theorem coe_sup (f g : SimpleFunc X) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g := rfl

theorem add_apply (f g : SimpleFunc X) (x : X) : (f + g) x = f x + g x := rfl
theorem mul_apply (f g : SimpleFunc X) (x : X) : (f * g) x = f x * g x := rfl
theorem sup_apply (f g : SimpleFunc X) (x : X) : (f ⊔ g) x = f x ⊔ g x := rfl

instance instPreorder : Preorder (SimpleFunc X) := Preorder.lift (⇑)

@[simp, norm_cast, gcongr] lemma coe_le_coe {f g : SimpleFunc X} : ⇑f ≤ g ↔ f ≤ g := Iff.rfl
@[simp, norm_cast, gcongr] lemma coe_lt_coe {f g : SimpleFunc X} : ⇑f < g ↔ f < g := Iff.rfl

instance instPartialOrder : PartialOrder (SimpleFunc X) :=
  { SimpleFunc.instPreorder with
    le_antisymm := fun _ _ hfg hgf ↦ ext fun x ↦ le_antisymm (hfg x) (hgf x) }

instance instOrderBot : OrderBot (SimpleFunc X) where
  bot := 0
  bot_le _ _ := bot_le

instance instSemilatticeSup : SemilatticeSup (SimpleFunc X) :=
  { SimpleFunc.instPartialOrder with
  sup := (· ⊔ ·)
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h₁ h₂ x := sup_le (h₁ x) (h₂ x)
  }

theorem finset_sup_apply {ι : Type*} {f : ι → SimpleFunc X} (s : Finset ι) (x : X) :
    s.sup f x = s.sup fun i ↦ f i x := by
  classical
  refine Finset.induction_on s rfl ?_
  intro a s _ ih
  rw [Finset.sup_insert, Finset.sup_insert, sup_apply, ih]

section Restrict

open scoped Classical in
/-- Restriction of a simple function to a measurable set. -/
def restrict (f : SimpleFunc X) (s : Set X) : SimpleFunc X :=
  if hs : MeasurableSet s then piecewise s hs f 0 else 0

theorem restrict_of_not_measurable {f : SimpleFunc X} {s : Set X} (hs : ¬ MeasurableSet s) :
    restrict f s = 0 := by
  simp [SimpleFunc.restrict, hs]

@[simp]
theorem coe_restrict (f : SimpleFunc X) {s : Set X} (hs : MeasurableSet s) :
    ⇑(restrict f s) = Set.indicator s f := by
  classical
  rw [restrict, dif_pos hs, coe_piecewise, coe_zero, piecewise_eq_indicator]

theorem restrict_apply (f : SimpleFunc X) {s : Set X} (hs : MeasurableSet s) (x : X) :
    restrict f s x = Set.indicator s f x := by
  simp [f.coe_restrict hs]

theorem restrict_preimage_singleton (f : SimpleFunc X) {s : Set X} (hs : MeasurableSet s)
    {r : ℝ≥0∞} (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} := by
  ext x
  by_cases hx : x ∈ s <;> simp [hs, hx]; grind

end Restrict

section Approx

/-- A sequence enumerating the nonnegative rational numbers in `ℝ≥0∞`. -/
def ennrealRatEmbed (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Encodable.decode (α := ℚ) n).getD (0 : ℚ))

theorem ennrealRatEmbed_encode (q : ℚ) :
    ennrealRatEmbed (Encodable.encode q) = Real.toNNReal q := by
  rw [ennrealRatEmbed, Encodable.encodek]
  rfl

/-- Simple approximation of a measurable `ℝ≥0∞`-valued function. -/
def approx (i : ℕ → ℝ≥0∞) (f : X → ℝ≥0∞) (n : ℕ) : SimpleFunc X :=
  (Finset.range n).sup fun k ↦ restrict (const X (i k)) {x : X | i k ≤ f x}

theorem approx_apply {i : ℕ → ℝ≥0∞} {f : X → ℝ≥0∞} {n : ℕ} (x : X) (hf : Measurable f) :
    (approx i f n : SimpleFunc X) x =
      (Finset.range n).sup fun k ↦ if i k ≤ f x then i k else 0 := by
  dsimp [approx]
  rw [finset_sup_apply]
  congr with k
  rw [restrict_apply]
  · simp [indicator_apply]
  · refine measurableSet_le measurable_const hf

theorem monotone_approx (i : ℕ → ℝ≥0∞) (f : X → ℝ≥0∞) : Monotone (approx i f) := fun _ _ h ↦
  Finset.sup_mono <| Finset.range_subset_range.2 h

theorem iSup_approx_apply (i : ℕ → ℝ≥0∞) (f : X → ℝ≥0∞) (x : X) (hf : Measurable f) :
    ⨆ n, approx i f n x = ⨆ (k) (_ : i k ≤ f x), i k := by
  refine le_antisymm (iSup_le fun n ↦ ?_) (iSup_le fun k ↦ iSup_le fun hk ↦ ?_)
  · rw [approx_apply x hf]
    refine Finset.sup_le fun k _ ↦ ?_
    split_ifs with hki
    · exact le_iSup_of_le k (le_iSup (fun _ : i k ≤ f x ↦ i k) hki)
    · exact bot_le
  · refine le_iSup_of_le (k + 1) ?_
    rw [approx_apply x hf]
    have hk_mem : k ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_self _)
    refine le_trans ?_ (Finset.le_sup hk_mem)
    rw [if_pos hk]

/-- Approximation by nonnegative rational values. -/
def eapprox (f : X → ℝ≥0∞) (n : ℕ) : SimpleFunc X :=
  (Finset.range n).sup fun k ↦
    restrict (const X (ennrealRatEmbed k)) {x : X | ennrealRatEmbed k ≤ f x}

theorem eapprox_apply {f : X → ℝ≥0∞} {n : ℕ} (x : X) (hf : Measurable f) :
    eapprox f n x =
      (Finset.range n).sup fun k ↦
        if ennrealRatEmbed k ≤ f x then ennrealRatEmbed k else 0 := by
  dsimp [eapprox]
  rw [finset_sup_apply]
  congr with k
  rw [restrict_apply]
  · simp [indicator_apply]
  · refine measurableSet_le measurable_const hf

theorem eapprox_lt_top (f : X → ℝ≥0∞) (n : ℕ) (x : X) : eapprox f n x < ∞ := by
  classical
  simp only [eapprox, finset_sup_apply, restrict]
  rw [Finset.sup_lt_iff (α := ℝ≥0∞) WithTop.top_pos]
  intro b hb
  split_ifs
  · simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const]
    calc
      { x : X | ennrealRatEmbed b ≤ f x }.indicator (fun _ ↦ ennrealRatEmbed b) x ≤
          ennrealRatEmbed b :=
        indicator_le_self _ _ x
      _ < ∞ := ENNReal.coe_lt_top
  · exact WithTop.top_pos

@[gcongr, mono]
theorem monotone_eapprox (f : X → ℝ≥0∞) : Monotone (eapprox f) :=
  fun i j hij ↦ by
    apply Finset.sup_le
    intro k hk
    simp only [Finset.mem_range] at hk
    apply Finset.le_sup_of_le (b := k)
    · refine Finset.mem_range.mpr (by grind)
    · apply le_refl
  -- Finset.sup_mono (Finset.range_subset_range.mpr hij)

theorem iSup_eapprox_apply {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    ⨆ n, eapprox f n x = f x := by
  refine le_antisymm (iSup_le fun n ↦ ?_) ?_
  · rw [eapprox_apply x hf]
    refine Finset.sup_le fun k _ ↦ ?_
    split_ifs with hki
    · apply hki
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

end Approx

end Measurable

section Measure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ ν : Measure X}

/-- Integral of an `ℝ≥0∞`-valued simple function. -/
def lintegral (f : SimpleFunc X) (μ : Measure X) : ℝ≥0∞ :=
  ∑ x ∈ f.range, x * μ (f ⁻¹' {x})

theorem lintegral_eq_of_subset (f : SimpleFunc X) {s : Finset ℝ≥0∞}
    (hs : ∀ x, f x ≠ 0 → μ (f ⁻¹' {f x}) ≠ 0 → f x ∈ s) :
    f.lintegral μ = ∑ x ∈ s, x * μ (f ⁻¹' {x}) := by
  refine Finset.sum_bij_ne_zero (fun r _ _ ↦ r) ?_ ?_ ?_ ?_
  · simpa only [forall_mem_range, mul_ne_zero_iff, and_imp]
  · intro x _ _
    simp
  · intro b _ hb
    refine ⟨b, ?_, hb, rfl⟩
    rw [mem_range, ← preimage_singleton_nonempty]
    exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2
  · intro _ _ _
    rfl

theorem lintegral_eq_of_subset' (f : SimpleFunc X) {s : Finset ℝ≥0∞} (hs : f.range \ {0} ⊆ s) :
    f.lintegral μ = ∑ x ∈ s, x * μ (f ⁻¹' {x}) :=
  f.lintegral_eq_of_subset fun x hx _ ↦
    hs <| Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hx⟩

theorem map_lintegral (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc X) :
    (f.map g).lintegral μ = ∑ x ∈ f.range, g x * μ (f ⁻¹' {x}) := by
  simp only [lintegral, range_map]
  refine Finset.sum_image' _ fun b hb ↦ ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton, Finset.mul_sum]
  refine Finset.sum_congr ?_ ?_
  · congr
  · intro x hx
    simp only [Finset.mem_filter, mem_range] at hx
    simp [hx.2]

theorem lintegral_restrict (f : SimpleFunc X) (s : Set X) (μ : Measure X) :
    f.lintegral (μ.restrict s) = ∑ y ∈ f.range, y * μ (f ⁻¹' {y} ∩ s) := by
  simp only [lintegral, Measure.restrict_apply, f.measurableSet_preimage]

theorem lintegral_partition (f g : SimpleFunc X) (μ : Measure X) :
    g.lintegral μ = ∑ r ∈ f.range, g.lintegral (μ.restrict (f ⁻¹' {r})) := by
  rw [lintegral]
  calc
    ∑ y ∈ g.range, y * μ (g ⁻¹' {y}) =
        ∑ y ∈ g.range, y * ∑ r ∈ f.range, μ (f ⁻¹' {r} ∩ g ⁻¹' {y}) := by
          refine Finset.sum_congr rfl fun y hy ↦ ?_
          congr 1
          have hsum := f.sum_measure_preimage_singleton (μ := μ.restrict (g ⁻¹' {y})) f.range
          simpa [Measure.restrict_apply, f.measurableSet_preimage, inter_comm, inter_left_comm,
            f.coe_range] using hsum.symm
    _ = ∑ r ∈ f.range, ∑ y ∈ g.range, y * μ (g ⁻¹' {y} ∩ f ⁻¹' {r}) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [inter_comm]
    _ = ∑ r ∈ f.range, g.lintegral (μ.restrict (f ⁻¹' {r})) := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          rw [g.lintegral_restrict]

open scoped Classical in
theorem restrict_lintegral (f : SimpleFunc X) {s : Set X} (hs : MeasurableSet s) :
    (f.restrict s).lintegral μ = ∑ r ∈ f.range, r * μ (f ⁻¹' {r} ∩ s) := by
  calc
    (f.restrict s).lintegral μ = ∑ r ∈ f.range, r * μ (f.restrict s ⁻¹' {r}) := by
      refine lintegral_eq_of_subset _ fun x hx ↦
        if hxs : x ∈ s then fun _ ↦ by
          simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
        else False.elim <| hx <| by simp [f.restrict_apply hs, hxs]
    _ = ∑ r ∈ f.range, r * μ (f ⁻¹' {r} ∩ s) := by
      refine Finset.sum_congr rfl <| forall_mem_range.2 fun b ↦
        if hb : f b = 0 then by simp [hb]
        else by rw [restrict_preimage_singleton _ hs hb, inter_comm]

theorem restrict_lintegral_eq_lintegral_restrict (f : SimpleFunc X) {s : Set X}
    (hs : MeasurableSet s) : (f.restrict s).lintegral μ = f.lintegral (μ.restrict s) := by
  rw [f.restrict_lintegral hs, f.lintegral_restrict]

theorem const_lintegral (c : ℝ≥0∞) :
    (SimpleFunc.const X c).lintegral μ = c * μ univ := by
  rw [lintegral]
  cases isEmpty_or_nonempty X with
  | inl h =>
      simp [Measure.eq_zero_of_isEmpty (μ := μ)]
  | inr h =>
      simp only [range_const, coe_const, Finset.sum_singleton]
      unfold Function.const
      rw [preimage_const_of_mem (mem_singleton c)]

theorem restrict_const_lintegral (c : ℝ≥0∞) {s : Set X} (hs : MeasurableSet s) :
    ((SimpleFunc.const X c).restrict s).lintegral μ = c * μ s := by
  rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral,
    Measure.restrict_apply MeasurableSet.univ, univ_inter]

theorem const_add_lintegral (f : SimpleFunc X) (c : ℝ≥0∞) :
    (SimpleFunc.const X c + f).lintegral μ = c * μ univ + f.lintegral μ := by
  have hmap : SimpleFunc.const X c + f = f.map (fun a ↦ c + a) := by
    ext x
    simp [map_apply]
  rw [hmap, map_lintegral]
  calc
    ∑ r ∈ f.range, (c + r) * μ (f ⁻¹' {r}) =
        ∑ r ∈ f.range, (c * μ (f ⁻¹' {r}) + r * μ (f ⁻¹' {r})) := by
          refine Finset.sum_congr rfl fun r hr ↦ by rw [add_mul]
    _ = (∑ r ∈ f.range, c * μ (f ⁻¹' {r})) + ∑ r ∈ f.range, r * μ (f ⁻¹' {r}) := by
          rw [Finset.sum_add_distrib]
    _ = c * μ univ + f.lintegral μ := by
          rw [← Finset.mul_sum, f.sum_range_measure_preimage_singleton, lintegral]

theorem const_mul_lintegral (f : SimpleFunc X) (c : ℝ≥0∞) :
    (SimpleFunc.const X c * f).lintegral μ = c * f.lintegral μ := by
  have hmap : SimpleFunc.const X c * f = f.map (fun a ↦ c * a) := by
    ext x
    simp [map_apply]
  rw [hmap, lintegral, range_map]
  calc
    ∑ b ∈ f.range.image (fun a ↦ c * a), b * μ ((f.map fun a ↦ c * a) ⁻¹' {b}) =
        ∑ b ∈ f.range.image (fun a ↦ c * a),
          b * ∑ a ∈ f.range with c * a = b, μ (f ⁻¹' {a}) := by
            refine Finset.sum_congr rfl fun b hb ↦ ?_
            rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton]
    _ = ∑ b ∈ f.range.image (fun a ↦ c * a),
          ∑ a ∈ f.range with c * a = b, b * μ (f ⁻¹' {a}) := by
            refine Finset.sum_congr rfl fun b hb ↦ ?_
            rw [Finset.mul_sum]
    _ = ∑ b ∈ f.range.image (fun a ↦ c * a),
          ∑ a ∈ f.range with c * a = b, (c * a) * μ (f ⁻¹' {a}) := by
            refine Finset.sum_congr rfl fun b hb ↦ ?_
            refine Finset.sum_congr rfl fun a ha ↦ ?_
            simp only [Finset.mem_filter] at ha
            rw [ha.2]
    _ = ∑ a ∈ f.range, (c * a) * μ (f ⁻¹' {a}) := by
          exact
            (Finset.sum_fiberwise_of_maps_to
              (s := f.range)
              (t := f.range.image (fun a ↦ c * a))
              (g := fun a ↦ c * a)
              (h := fun a ha ↦ Finset.mem_image.2 ⟨a, ha, rfl⟩)
              (f := fun a ↦ (c * a) * μ (f ⁻¹' {a})))
    _ = ∑ a ∈ f.range, c * (a * μ (f ⁻¹' {a})) := by
          refine Finset.sum_congr rfl fun a ha ↦ ?_
          rw [mul_assoc]
    _ = c * ∑ a ∈ f.range, a * μ (f ⁻¹' {a}) := by rw [Finset.mul_sum]
    _ = c * f.lintegral μ := by rw [lintegral]

theorem zero_lintegral : (0 : SimpleFunc X).lintegral μ = 0 := by
  simpa using (const_lintegral (X := X) (μ := μ) 0)

theorem add_lintegral (f g : SimpleFunc X) :
    (f + g).lintegral μ = f.lintegral μ + g.lintegral μ := by
  calc
    (f + g).lintegral μ = ∑ r ∈ f.range, (f + g).lintegral (μ.restrict (f ⁻¹' {r})) := by
      exact f.lintegral_partition (g := f + g) μ
    _ = ∑ r ∈ f.range, (SimpleFunc.const X r + g).lintegral (μ.restrict (f ⁻¹' {r})) := by
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      rw [← restrict_lintegral_eq_lintegral_restrict _ (f.measurableSet_fiber r)]
      rw [← restrict_lintegral_eq_lintegral_restrict _ (f.measurableSet_fiber r)]
      refine congrArg (fun h : SimpleFunc X ↦ h.lintegral μ) ?_
      ext x
      by_cases hx : x ∈ f ⁻¹' {r}
      · have hfx : f x = r := by simpa using hx
        simp [restrict_apply, f.measurableSet_fiber, hx, hfx]
      · simp [restrict_apply, f.measurableSet_fiber, hx]
    _ = ∑ r ∈ f.range,
          (r * (μ.restrict (f ⁻¹' {r})) univ + g.lintegral (μ.restrict (f ⁻¹' {r}))) := by
      refine Finset.sum_congr rfl fun r hr ↦ by
        simpa using (const_add_lintegral (μ := μ.restrict (f ⁻¹' {r})) g r)
    _ = ∑ r ∈ f.range, (r * μ (f ⁻¹' {r}) + g.lintegral (μ.restrict (f ⁻¹' {r}))) := by
      refine Finset.sum_congr rfl fun r hr ↦ by
        rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    _ = (∑ r ∈ f.range, r * μ (f ⁻¹' {r})) + ∑ r ∈ f.range,
          g.lintegral (μ.restrict (f ⁻¹' {r})) := by
      rw [Finset.sum_add_distrib]
    _ = f.lintegral μ + g.lintegral μ := by
      rw [lintegral, f.lintegral_partition (g := g) μ]

theorem lintegral_mono_measure {f : SimpleFunc X} (hμν : μ ≤ ν) :
    f.lintegral μ ≤ f.lintegral ν := by
  rw [lintegral, lintegral]
  gcongr

theorem lintegral_mono_fun {f g : SimpleFunc X} (hfg : f ≤ g) : f.lintegral μ ≤ g.lintegral μ := by
  calc
    f.lintegral μ = ∑ r ∈ f.range, r * μ (f ⁻¹' {r}) := rfl
    _ ≤ ∑ r ∈ f.range, g.lintegral (μ.restrict (f ⁻¹' {r})) := by
      refine Finset.sum_le_sum fun r hr ↦ ?_
      have hsum := g.sum_measure_preimage_singleton (μ := μ.restrict (f ⁻¹' {r})) g.range
      calc
        r * μ (f ⁻¹' {r}) = ∑ y ∈ g.range, r * μ (g ⁻¹' {y} ∩ f ⁻¹' {r}) := by
          simpa [Measure.restrict_apply, g.measurableSet_preimage, inter_comm, Finset.mul_sum] using
            congrArg (fun z ↦ r * z) hsum.symm
        _ ≤ ∑ y ∈ g.range, y * μ (g ⁻¹' {y} ∩ f ⁻¹' {r}) := by
          refine Finset.sum_le_sum fun y hy ↦ ?_
          by_cases hμ0 : μ (g ⁻¹' {y} ∩ f ⁻¹' {r}) = 0
          · simp [hμ0]
          · rcases nonempty_of_measure_ne_zero hμ0 with ⟨x, hx⟩
            have hxg : g x = y := by simpa using hx.1
            have hxf : f x = r := by simpa using hx.2
            gcongr
            simpa [hxf, hxg] using hfg x
        _ = g.lintegral (μ.restrict (f ⁻¹' {r})) := by
          rw [g.lintegral_restrict]
    _ = g.lintegral μ := (f.lintegral_partition (g := g) μ).symm

@[mono, gcongr]
theorem lintegral_mono {f g : SimpleFunc X} (hfg : f ≤ g) (hμν : μ ≤ ν) :
    f.lintegral μ ≤ g.lintegral ν :=
  (f.lintegral_mono_fun hfg).trans (g.lintegral_mono_measure hμν)

theorem lintegral_eq_of_measure_preimage {f : SimpleFunc X} {g : SimpleFunc Y}
    {ν : Measure Y} (h : ∀ y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) : f.lintegral μ = g.lintegral ν := by
  simp only [lintegral, ← h]
  apply lintegral_eq_of_subset
  simp only [h]
  intro x _ hx
  exact mem_range_of_measure_ne_zero hx

theorem lintegral_congr {f g : SimpleFunc X} (h : f =ᵐ[μ] g) :
    f.lintegral μ = g.lintegral μ :=
  lintegral_eq_of_measure_preimage fun y ↦
    measure_congr <| Eventually.set_eq <| h.mono fun x hx ↦ by simp [hx]

-- theorem lintegral_map' [MeasurableSpace Y] {μ' : Measure Y} (f : SimpleFunc X) (g : SimpleFunc Y)
--     (m' : X → Y) (hfg : ∀ x, f x = g (m' x))
--     (hm : ∀ s, MeasurableSet s → μ' s = μ (m' ⁻¹' s)) :
--     f.lintegral μ = g.lintegral μ' :=
--   sorry

-- theorem lintegral_map [MeasurableSpace Y] (g : SimpleFunc Y) {f : X → Y} (hf : Measurable f) :
--     g.lintegral (Measure.map f μ) = (g.comp f hf).lintegral μ := by
--   exact Eq.symm <| lintegral_map' _ _ f (fun _ ↦ rfl) fun s hs ↦ Measure.map_apply hf hs

end Measure

/-- Induction principle for `ℝ≥0∞`-valued simple functions. -/
@[elab_as_elim]
protected theorem induction {X : Type*} [MeasurableSpace X]
    {motive : SimpleFunc X → Prop}
    (const : ∀ (c : ℝ≥0∞) {s} (hs : MeasurableSet s),
      motive (SimpleFunc.piecewise s hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0)))
    (add : ∀ ⦃f g : SimpleFunc X⦄, Disjoint (support f) (support g) →
      motive f → motive g → motive (f + g))
    (f : SimpleFunc X) : motive f := by
  classical
  generalize hs : f.range \ {0} = s
  rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, SimpleFunc.coe_range] at hs
  induction s using Finset.induction generalizing f with
  | empty =>
      rw [Finset.coe_empty, diff_eq_empty, range_subset_singleton] at hs
      convert const 0 MeasurableSet.univ
      ext x
      simp [hs]
  | insert x s hxs ih =>
      have hxmeas := f.measurableSet_preimage {x}
      let g := SimpleFunc.piecewise (f ⁻¹' {x}) hxmeas 0 f
      have hg : motive g := by
        apply ih
        simp only [g, SimpleFunc.coe_piecewise, range_piecewise]
        rw [image_compl_preimage, union_diff_distrib, diff_diff_comm, hs, Finset.coe_insert,
          insert_diff_self_of_notMem, diff_eq_empty.mpr, Set.empty_union]
        · rw [Set.image_subset_iff]
          convert Set.subset_univ _
          exact preimage_const_of_mem (mem_singleton _)
        · rwa [Finset.mem_coe]
      convert add ?_ hg (const x hxmeas)
      · ext y
        by_cases hy : y ∈ f ⁻¹' {x}
        · simpa [g, hy]
        · simp [g, hy]
      · rw [disjoint_iff_inf_le]
        intro y
        by_cases hy : y ∈ f ⁻¹' {x} <;> simp [g, hy]

end SimpleFunc

open MeasureTheory SimpleFunc

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-- To prove something for an arbitrary measurable `ℝ≥0∞`-valued function, it suffices to check
indicator functions, sums on disjoint supports, and suprema of increasing sequences. -/
@[elab_as_elim]
theorem Measurable.ennreal_induction
    {motive : (X → ℝ≥0∞) → Prop}
    (indicator : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → motive (Set.indicator s fun _ ↦ c))
    (add : ∀ ⦃f g : X → ℝ≥0∞⦄, Disjoint (support f) (support g) →
      Measurable f → Measurable g → motive f → motive g → motive (f + g))
    (iSup : ∀ ⦃f : ℕ → X → ℝ≥0∞⦄, (∀ n, Measurable (f n)) → Monotone f →
      (∀ n, motive (f n)) → motive fun x ↦ ⨆ n, f n x)
    ⦃f : X → ℝ≥0∞⦄ (hf : Measurable f) : motive f := by
  convert
    iSup
      (fun n ↦ (SimpleFunc.eapprox f n).measurable)
      (SimpleFunc.monotone_eapprox f) _
      using 2
  · rw [SimpleFunc.iSup_eapprox_apply hf]
  · intro n
    exact SimpleFunc.induction (fun c s hs ↦ indicator c hs)
      (fun f g hfg hf hg ↦ add hfg f.measurable g.measurable hf hg) (SimpleFunc.eapprox f n)

end MTI
