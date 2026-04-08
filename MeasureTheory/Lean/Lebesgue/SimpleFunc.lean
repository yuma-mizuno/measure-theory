import MeasureTheory.Lean.Lebesgue.MeasurableCaratheodory
import Mathlib.Algebra.Algebra.Pi

set_option autoImplicit false

noncomputable section

open Set hiding restrict restrict_apply
open Function ENNReal

namespace MTI

namespace Real

/-- An `ℝ≥0∞`-valued simple function on `ℝ` with respect to the inductively defined measurable
sets. -/
structure SimpleFunc where
  /-- The underlying function. -/
  toFun : ℝ → ℝ≥0∞
  measurableSet_fiber' : ∀ x, MeasurableSet (toFun ⁻¹' {x})
  finite_range' : (Set.range toFun).Finite

namespace SimpleFunc

instance instFunLike : FunLike SimpleFunc ℝ ℝ≥0∞ where
  coe := SimpleFunc.toFun
  coe_injective' | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

theorem coe_injective ⦃f g : SimpleFunc⦄ (h : (f : ℝ → ℝ≥0∞) = g) : f = g :=
  DFunLike.ext' h

@[ext]
theorem ext {f g : SimpleFunc} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

theorem finite_range (f : SimpleFunc) : (Set.range f).Finite :=
  f.finite_range'

theorem measurableSet_fiber (f : SimpleFunc) (x : ℝ≥0∞) : MeasurableSet (f ⁻¹' {x}) :=
  f.measurableSet_fiber' x

@[simp] theorem coe_mk (f : ℝ → ℝ≥0∞) (h h') : ⇑(SimpleFunc.mk f h h') = f := rfl

theorem apply_mk (f : ℝ → ℝ≥0∞) (h h') (x : ℝ) : SimpleFunc.mk f h h' x = f x := rfl

/-- The finite range of a simple function as a finset. -/
protected def range (f : SimpleFunc) : Finset ℝ≥0∞ :=
  f.finite_range.toFinset

@[simp]
theorem mem_range {f : SimpleFunc} {x : ℝ≥0∞} : x ∈ f.range ↔ x ∈ Set.range f :=
  Finite.mem_toFinset _

theorem mem_range_self (f : SimpleFunc) (x : ℝ) : f x ∈ f.range :=
  mem_range.2 ⟨x, rfl⟩

@[simp]
theorem coe_range (f : SimpleFunc) : (↑f.range : Set ℝ≥0∞) = Set.range f :=
  f.finite_range.coe_toFinset

theorem forall_mem_range {f : SimpleFunc} {p : ℝ≥0∞ → Prop} :
    (∀ y ∈ f.range, p y) ↔ ∀ x, p (f x) := by
  simp only [mem_range, Set.forall_mem_range]

theorem preimage_eq_empty_iff (f : SimpleFunc) (x : ℝ≥0∞) :
    f ⁻¹' {x} = ∅ ↔ x ∉ f.range :=
  preimage_singleton_eq_empty.trans <| not_congr mem_range.symm

/-- Constant simple function. -/
def const (c : ℝ≥0∞) : SimpleFunc :=
  ⟨fun _ ↦ c, fun y ↦ by
    by_cases hy : y = c
    · have hpre : ((fun _ : ℝ ↦ c) ⁻¹' {y}) = Set.univ := by
        ext x
        simp [hy]
      simpa [hpre] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
    · have hpre : ((fun _ : ℝ ↦ c) ⁻¹' {y}) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro x hx
        have hc : c = y := by simpa using hx
        exact hy hc.symm
      simpa [hpre] using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ)),
   finite_range_const⟩

instance : Inhabited SimpleFunc := ⟨const 0⟩

theorem const_apply (x : ℝ) (c : ℝ≥0∞) : const c x = c := by
  simp [const]

@[simp]
theorem coe_const (c : ℝ≥0∞) : ⇑(const c) = Function.const ℝ c := by
  funext x
  simp [const]

@[simp]
theorem range_const (c : ℝ≥0∞) : (const c).range = {c} :=
  Finset.coe_injective <| by simp +unfoldPartialApp [Function.const]

theorem measurableSet_cut (r : ℝ → ℝ≥0∞ → Prop) (f : SimpleFunc)
    (h : ∀ y, MeasurableSet {x | r x y}) : MeasurableSet {x | r x (f x)} := by
  have h_union : {x | r x (f x)} = ⋃ y ∈ Set.range f, {x | r x y} ∩ f ⁻¹' {y} := by
    ext x
    suffices r x (f x) ↔ ∃ i, r x (f i) ∧ f x = f i by simpa
    exact ⟨fun hx ↦ ⟨x, ⟨hx, rfl⟩⟩, fun ⟨i, hi⟩ ↦ hi.2.symm ▸ hi.1⟩
  rw [h_union]
  exact MeasurableSet.biUnion f.finite_range.countable fun y _ ↦
    (h y).inter (f.measurableSet_fiber y)

theorem measurableSet_preimage (f : SimpleFunc) (s : Set ℝ≥0∞) :
    MeasurableSet (f ⁻¹' s) :=
  measurableSet_cut (fun _ y ↦ y ∈ s) f fun y ↦ by
    by_cases hy : y ∈ s
    · simpa [hy] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
    · simpa [hy] using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))

open scoped Classical in
/-- Piecewise combination of simple functions. -/
def piecewise (s : Set ℝ) (hs : MeasurableSet s) (f g : SimpleFunc) : SimpleFunc :=
  ⟨s.piecewise f g, fun y ↦ by
    have hpre :
        s.piecewise f g ⁻¹' {y} = (f ⁻¹' {y} ∩ s) ∪ (g ⁻¹' {y} ∩ sᶜ) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hpre]
    exact ((f.measurableSet_fiber y).inter hs).union
      ((g.measurableSet_fiber y).inter hs.compl),
   (f.finite_range.union g.finite_range).subset range_ite_subset⟩

open scoped Classical in
@[simp]
theorem coe_piecewise {s : Set ℝ} (hs : MeasurableSet s) (f g : SimpleFunc) :
    ⇑(piecewise s hs f g) = s.piecewise f g := rfl

open scoped Classical in
theorem piecewise_apply {s : Set ℝ} (hs : MeasurableSet s) (f g : SimpleFunc) (x : ℝ) :
    piecewise s hs f g x = if x ∈ s then f x else g x := rfl

@[simp]
theorem piecewise_univ (f g : SimpleFunc) :
    piecewise univ MeasurableSet.univ f g = f := by
  ext x
  simp [piecewise_apply]

@[simp]
theorem piecewise_empty (f g : SimpleFunc) :
    piecewise ∅ MeasurableSet.empty f g = g := by
  ext x
  simp [piecewise_apply]

/-- Pointwise endomorphism of simple functions. -/
def map (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc) : SimpleFunc where
  toFun := g ∘ f
  measurableSet_fiber' y := f.measurableSet_preimage {x | g x = y}
  finite_range' := by
    refine (f.range.image g).finite_toSet.subset ?_
    apply subset_of_eq
    rw [@Finset.coe_image, @coe_range, @range_comp]

@[simp]
theorem map_apply (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc) (x : ℝ) : f.map g x = g (f x) := rfl

@[simp]
theorem coe_map (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc) : (f.map g : ℝ → ℝ≥0∞) = g ∘ f := rfl

@[simp]
theorem range_map (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc) : (f.map g).range = f.range.image g :=
  Finset.coe_injective <| by simp only [coe_range, coe_map, Finset.coe_image, range_comp]

open scoped Classical in
theorem map_preimage_singleton (f : SimpleFunc) (g : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0∞) :
    f.map g ⁻¹' {c} = f ⁻¹' ↑{b ∈ f.range | g b = c} := by
  ext x
  simp

/-- Pointwise binary operation on simple functions. -/
def map₂ (f g : SimpleFunc) (op : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : SimpleFunc where
  toFun := fun x ↦ op (f x) (g x)
  measurableSet_fiber' c :=
    f.measurableSet_cut (fun x a ↦ op a (g x) = c) fun a ↦
      g.measurableSet_preimage {b | op a b = c}
  finite_range' :=
    ((f.range.product g.range).image fun p : ℝ≥0∞ × ℝ≥0∞ ↦ op p.1 p.2).finite_toSet.subset <| by
      rintro _ ⟨x, rfl⟩
      simp

theorem map₂_apply (f g : SimpleFunc) (op : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (x : ℝ) :
    f.map₂ g op x = op (f x) (g x) := rfl

instance : Zero SimpleFunc := ⟨const 0⟩
instance : Add SimpleFunc := ⟨fun f g ↦ f.map₂ g (· + ·)⟩
instance : Mul SimpleFunc := ⟨fun f g ↦ f.map₂ g (· * ·)⟩
instance : Max SimpleFunc := ⟨fun f g ↦ f.map₂ g max⟩
instance : LE SimpleFunc := ⟨fun f g ↦ ∀ x, f x ≤ g x⟩

@[simp, norm_cast] theorem coe_zero : ⇑(0 : SimpleFunc) = (0 : ℝ → ℝ≥0∞) := by
  funext x
  change const 0 x = 0
  simp [const_apply]
@[simp, norm_cast] theorem coe_add (f g : SimpleFunc) : ⇑(f + g) = ⇑f + ⇑g := rfl
@[simp, norm_cast] theorem coe_mul (f g : SimpleFunc) : ⇑(f * g) = ⇑f * ⇑g := rfl
@[simp, norm_cast] theorem coe_sup (f g : SimpleFunc) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g := rfl

theorem add_apply (f g : SimpleFunc) (x : ℝ) : (f + g) x = f x + g x := rfl
theorem mul_apply (f g : SimpleFunc) (x : ℝ) : (f * g) x = f x * g x := rfl
theorem sup_apply (f g : SimpleFunc) (x : ℝ) : (f ⊔ g) x = f x ⊔ g x := rfl

instance instPreorder : Preorder SimpleFunc := Preorder.lift (⇑)

instance instPartialOrder : PartialOrder SimpleFunc :=
  PartialOrder.lift (⇑) coe_injective

instance instOrderBot : OrderBot SimpleFunc where
  bot := 0
  bot_le _ _ := by simp

instance instSemilatticeSup : SemilatticeSup SimpleFunc :=
  { SimpleFunc.instPartialOrder with
    sup := (· ⊔ ·)
    le_sup_left _ _ _ := le_sup_left
    le_sup_right _ _ _ := le_sup_right
    sup_le _ _ _ h₁ h₂ x := sup_le (h₁ x) (h₂ x) }

theorem finset_sup_apply {ι : Type*} {f : ι → SimpleFunc} (s : Finset ι) (x : ℝ) :
    s.sup f x = s.sup fun i ↦ f i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · change (⊥ : SimpleFunc) x = 0
    change (0 : SimpleFunc) x = 0
    simp
  intro a s _ ih
  rw [Finset.sup_insert, Finset.sup_insert, sup_apply, ih]

open scoped Classical in
/-- Restriction of a simple function to a measurable set. -/
def restrict (f : SimpleFunc) (s : Set ℝ) : SimpleFunc :=
  if hs : MeasurableSet s then piecewise s hs f 0 else 0

theorem restrict_of_not_measurable {f : SimpleFunc} {s : Set ℝ} (hs : ¬ MeasurableSet s) :
    restrict f s = 0 := by
  simp [SimpleFunc.restrict, hs]

@[simp]
theorem coe_restrict (f : SimpleFunc) {s : Set ℝ} (hs : MeasurableSet s) :
    ⇑(restrict f s) = Set.indicator s f := by
  classical
  rw [restrict, dif_pos hs, coe_piecewise, coe_zero, piecewise_eq_indicator]

theorem restrict_apply (f : SimpleFunc) {s : Set ℝ} (hs : MeasurableSet s) (x : ℝ) :
    restrict f s x = Set.indicator s f x := by
  simp [f.coe_restrict hs]

theorem restrict_preimage_singleton (f : SimpleFunc) {s : Set ℝ} (hs : MeasurableSet s)
    {r : ℝ≥0∞} (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} := by
  ext x
  by_cases hx : x ∈ s
  · simp [hs, hx]
  · simp [hs, hx, hr, eq_comm]

theorem nonempty_of_measure_ne_zero {s : Set ℝ} (hs : measure s ≠ 0) : s.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  simp [h] at hs

theorem mem_range_of_measure_ne_zero {f : SimpleFunc} {x : ℝ≥0∞}
    (h : measure (f ⁻¹' {x}) ≠ 0) : x ∈ f.range := by
  let ⟨a, ha⟩ := nonempty_of_measure_ne_zero h
  exact mem_range.2 ⟨a, ha⟩

/-- Integral of a simple function over a measurable set. -/
def lintegralIn (f : SimpleFunc) (s : Set ℝ) : ℝ≥0∞ :=
  ∑ x ∈ f.range, x * measure (f ⁻¹' {x} ∩ s)

/-- Integral of a simple function over `ℝ`. -/
def lintegral (f : SimpleFunc) : ℝ≥0∞ :=
  ∑ x ∈ f.range, x * measure (f ⁻¹' {x})

theorem lintegral_eq_lintegralIn_univ (f : SimpleFunc) :
    f.lintegral = f.lintegralIn univ := by
  rw [lintegral, lintegralIn]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  congr 2
  ext a
  simp

theorem lintegralIn_eq_of_subset (f : SimpleFunc) {s : Set ℝ} {t : Finset ℝ≥0∞}
    (ht : ∀ x, f x ≠ 0 → measure (f ⁻¹' {f x} ∩ s) ≠ 0 → f x ∈ t) :
    f.lintegralIn s = ∑ x ∈ t, x * measure (f ⁻¹' {x} ∩ s) := by
  refine Finset.sum_bij_ne_zero (fun r _ _ ↦ r) ?_ ?_ ?_ ?_
  · simpa only [forall_mem_range, mul_ne_zero_iff, and_imp]
  · intro x _ _
    simp
  · intro b _ hb
    refine ⟨b, ?_, hb, rfl⟩
    rw [mem_range, ← preimage_singleton_nonempty]
    exact (nonempty_of_measure_ne_zero <| (mul_ne_zero_iff.1 hb).2).mono fun x hx ↦ hx.1
  · intro _ _ _
    rfl

theorem lintegral_eq_of_subset (f : SimpleFunc) {t : Finset ℝ≥0∞}
    (ht : ∀ x, f x ≠ 0 → measure (f ⁻¹' {f x}) ≠ 0 → f x ∈ t) :
    f.lintegral = ∑ x ∈ t, x * measure (f ⁻¹' {x}) := by
  simpa [lintegral, lintegralIn] using
    f.lintegralIn_eq_of_subset (s := univ) fun x hx hμ ↦ by
      simpa using ht x hx (by simpa using hμ)

theorem lintegral_eq_of_subset' (f : SimpleFunc) {t : Finset ℝ≥0∞} (ht : f.range \ {0} ⊆ t) :
    f.lintegral = ∑ x ∈ t, x * measure (f ⁻¹' {x}) :=
  f.lintegral_eq_of_subset fun x hx _ ↦
    ht <| Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hx⟩

theorem lintegralIn_eq_of_subset' (f : SimpleFunc) {s : Set ℝ} {t : Finset ℝ≥0∞}
    (ht : ∀ x, f x ∈ f.range \ {0} → measure (f ⁻¹' {f x} ∩ s) ≠ 0 → f x ∈ t) :
    f.lintegralIn s = ∑ x ∈ t, x * measure (f ⁻¹' {x} ∩ s) := by
  refine f.lintegralIn_eq_of_subset ?_
  intro x hx hμ
  exact ht x (Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hx⟩) hμ

theorem sum_measure_preimage_singleton_in (f : SimpleFunc) {s : Set ℝ} (hs : MeasurableSet s)
    (t : Finset ℝ≥0∞) : (∑ y ∈ t, measure (f ⁻¹' {y} ∩ s)) = measure (f ⁻¹' ↑t ∩ s) := by
  classical
  let A : t → Set ℝ := fun y ↦ f ⁻¹' {(y : ℝ≥0∞)} ∩ s
  have hA : ∀ y : t, MeasurableSet (A y) := by
    intro y
    exact (f.measurableSet_fiber y).inter hs
  have hdisj : Pairwise (Disjoint on A) := by
    intro y z hyz
    refine Set.disjoint_left.2 ?_
    intro x hx hy
    exact hyz (Subtype.ext <| hx.1.symm.trans hy.1)
  have hcount : measure (⋃ y : t, A y) = ∑' y : t, measure (A y) :=
    measure_iUnion_countable hdisj hA
  have hUnion : (⋃ y : t, A y) = f ⁻¹' ↑t ∩ s := by
    ext x
    simp [A]
  calc
    ∑ y ∈ t, measure (f ⁻¹' {y} ∩ s) = ∑' y : t, measure (A y) := by
      simpa [A] using (t.tsum_subtype fun y ↦ measure (f ⁻¹' {y} ∩ s)).symm
    _ = measure (f ⁻¹' ↑t ∩ s) := by
      simpa [hUnion] using hcount.symm

theorem sum_range_measure_preimage_singleton_in (f : SimpleFunc) {s : Set ℝ} (hs : MeasurableSet s) :
    (∑ y ∈ f.range, measure (f ⁻¹' {y} ∩ s)) = measure s := by
  rw [f.sum_measure_preimage_singleton_in hs f.range]
  simp [coe_range]

theorem map_lintegralIn (g : ℝ≥0∞ → ℝ≥0∞) (f : SimpleFunc) {s : Set ℝ} (hs : MeasurableSet s) :
    (f.map g).lintegralIn s = ∑ x ∈ f.range, g x * measure (f ⁻¹' {x} ∩ s) := by
  classical
  simp only [lintegralIn, range_map]
  refine Finset.sum_image' _ fun a ha ↦ ?_
  rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton_in hs (f.range.filter fun x ↦ g x = g a),
    Finset.mul_sum]
  refine Finset.sum_congr ?_ ?_
  · congr
  · intro x hx
    simp only [Finset.mem_filter] at hx
    simp [hx.2]

theorem const_lintegralIn (c : ℝ≥0∞) {s : Set ℝ} (_hs : MeasurableSet s) :
    (SimpleFunc.const c).lintegralIn s = c * measure s := by
  rw [lintegralIn, range_const]
  simp only [Finset.sum_singleton, coe_const]
  congr 2
  ext x
  simp

theorem lintegralIn_partition (f g : SimpleFunc) {s : Set ℝ} (hs : MeasurableSet s) :
    g.lintegralIn s = ∑ r ∈ f.range, g.lintegralIn (f ⁻¹' {r} ∩ s) := by
  calc
    g.lintegralIn s =
        ∑ y ∈ g.range, y * ∑ r ∈ f.range, measure (f ⁻¹' {r} ∩ (g ⁻¹' {y} ∩ s)) := by
          rw [lintegralIn]
          refine Finset.sum_congr rfl fun y hy ↦ ?_
          have hys : MeasurableSet (g ⁻¹' {y} ∩ s) := (g.measurableSet_fiber y).inter hs
          have hsum :
              measure (g ⁻¹' {y} ∩ s) =
                ∑ r ∈ f.range, measure (f ⁻¹' {r} ∩ (g ⁻¹' {y} ∩ s)) := by
            simpa [f.coe_range, inter_assoc, inter_left_comm, inter_comm] using
              (f.sum_measure_preimage_singleton_in hys f.range).symm
          rw [hsum, Finset.mul_sum]
    _ = ∑ y ∈ g.range, ∑ r ∈ f.range, y * measure (g ⁻¹' {y} ∩ (f ⁻¹' {r} ∩ s)) := by
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          congr 2
          ext x
          simp [inter_assoc, inter_left_comm, inter_comm]
    _ = ∑ r ∈ f.range, ∑ y ∈ g.range, y * measure (g ⁻¹' {y} ∩ (f ⁻¹' {r} ∩ s)) := by
          rw [Finset.sum_comm]
    _ = ∑ r ∈ f.range, g.lintegralIn (f ⁻¹' {r} ∩ s) := by
          refine Finset.sum_congr rfl fun r _ ↦ by
            rw [lintegralIn]

theorem restrict_lintegral (f : SimpleFunc) {s : Set ℝ} (hs : MeasurableSet s) :
    (f.restrict s).lintegral = f.lintegralIn s := by
  calc
    (f.restrict s).lintegral = ∑ r ∈ f.range, r * measure (f.restrict s ⁻¹' {r}) := by
      refine lintegral_eq_of_subset _ fun x hx ↦ ?_
      by_cases hxs : x ∈ s
      · intro _
        simp [f.restrict_apply hs, hxs]
      · intro _
        exact False.elim <| hx <| by simp [f.restrict_apply hs, hxs]
    _ = ∑ r ∈ f.range, r * measure (f ⁻¹' {r} ∩ s) := by
      refine Finset.sum_congr rfl <| forall_mem_range.2 fun b ↦
        if hb : f b = 0 then by simp [hb]
        else by rw [restrict_preimage_singleton _ hs hb, inter_comm]
    _ = f.lintegralIn s := rfl

theorem lintegral_partition (f g : SimpleFunc) :
    g.lintegral = ∑ r ∈ f.range, g.lintegralIn (f ⁻¹' {r}) := by
  rw [g.lintegral_eq_lintegralIn_univ]
  simpa [inter_univ] using g.lintegralIn_partition (f := f) MeasurableSet.univ

theorem const_lintegral (c : ℝ≥0∞) :
    (SimpleFunc.const c).lintegral = c * measure univ := by
  rw [(SimpleFunc.const c).lintegral_eq_lintegralIn_univ]
  exact const_lintegralIn c MeasurableSet.univ

theorem restrict_const_lintegral (c : ℝ≥0∞) {s : Set ℝ} (hs : MeasurableSet s) :
    ((SimpleFunc.const c).restrict s).lintegral = c * measure s := by
  rw [restrict_lintegral _ hs, const_lintegralIn _ hs]

theorem const_add_lintegralIn (f : SimpleFunc) (c : ℝ≥0∞) {s : Set ℝ} (hs : MeasurableSet s) :
    (SimpleFunc.const c + f).lintegralIn s = c * measure s + f.lintegralIn s := by
  have hmap : SimpleFunc.const c + f = f.map (fun a ↦ c + a) := by
    ext x
    simp [map_apply]
  rw [hmap, map_lintegralIn _ _ hs]
  calc
    ∑ r ∈ f.range, (c + r) * measure (f ⁻¹' {r} ∩ s) =
        ∑ r ∈ f.range, (c * measure (f ⁻¹' {r} ∩ s) + r * measure (f ⁻¹' {r} ∩ s)) := by
          refine Finset.sum_congr rfl fun r _ ↦ by rw [add_mul]
    _ = (∑ r ∈ f.range, c * measure (f ⁻¹' {r} ∩ s)) +
          ∑ r ∈ f.range, r * measure (f ⁻¹' {r} ∩ s) := by
          rw [Finset.sum_add_distrib]
    _ = c * measure s + f.lintegralIn s := by
          rw [← Finset.mul_sum, f.sum_range_measure_preimage_singleton_in hs, lintegralIn]

theorem const_add_lintegral (f : SimpleFunc) (c : ℝ≥0∞) :
    (SimpleFunc.const c + f).lintegral = c * measure univ + f.lintegral := by
  rw [(SimpleFunc.const c + f).lintegral_eq_lintegralIn_univ, f.lintegral_eq_lintegralIn_univ]
  exact f.const_add_lintegralIn c MeasurableSet.univ

theorem const_mul_lintegralIn (f : SimpleFunc) (c : ℝ≥0∞) {s : Set ℝ} (hs : MeasurableSet s) :
    (SimpleFunc.const c * f).lintegralIn s = c * f.lintegralIn s := by
  have hmap : SimpleFunc.const c * f = f.map (fun a ↦ c * a) := by
    ext x
    simp [map_apply]
  rw [hmap, lintegralIn, range_map]
  calc
    ∑ b ∈ f.range.image (fun a ↦ c * a), b * measure ((f.map fun a ↦ c * a) ⁻¹' {b} ∩ s) =
        ∑ b ∈ f.range.image (fun a ↦ c * a),
          b * ∑ a ∈ f.range with c * a = b, measure (f ⁻¹' {a} ∩ s) := by
            refine Finset.sum_congr rfl fun b hb ↦ ?_
            rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton_in hs
              (f.range.filter fun a ↦ c * a = b), Finset.mul_sum]
    _ = ∑ b ∈ f.range.image (fun a ↦ c * a),
          ∑ a ∈ f.range with c * a = b, b * measure (f ⁻¹' {a} ∩ s) := by
            refine Finset.sum_congr rfl fun b hb ↦ ?_
            rw [Finset.mul_sum]
    _ = ∑ b ∈ f.range.image (fun a ↦ c * a),
          ∑ a ∈ f.range with c * a = b, (c * a) * measure (f ⁻¹' {a} ∩ s) := by
            refine Finset.sum_congr rfl fun b hb ↦ ?_
            refine Finset.sum_congr rfl fun a ha ↦ ?_
            simp only [Finset.mem_filter] at ha
            rw [ha.2]
    _ = ∑ a ∈ f.range, (c * a) * measure (f ⁻¹' {a} ∩ s) := by
          exact
            (Finset.sum_fiberwise_of_maps_to
              (s := f.range)
              (t := f.range.image (fun a ↦ c * a))
              (g := fun a ↦ c * a)
              (h := fun a ha ↦ Finset.mem_image.2 ⟨a, ha, rfl⟩)
              (f := fun a ↦ (c * a) * measure (f ⁻¹' {a} ∩ s)))
    _ = ∑ a ∈ f.range, c * (a * measure (f ⁻¹' {a} ∩ s)) := by
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [mul_assoc]
    _ = c * ∑ a ∈ f.range, a * measure (f ⁻¹' {a} ∩ s) := by
          rw [Finset.mul_sum]
    _ = c * f.lintegralIn s := by
          rw [lintegralIn]

theorem const_mul_lintegral (f : SimpleFunc) (c : ℝ≥0∞) :
    (SimpleFunc.const c * f).lintegral = c * f.lintegral := by
  rw [(SimpleFunc.const c * f).lintegral_eq_lintegralIn_univ, f.lintegral_eq_lintegralIn_univ]
  exact f.const_mul_lintegralIn c MeasurableSet.univ

theorem zero_lintegral : (0 : SimpleFunc).lintegral = 0 := by
  simpa using (const_lintegral 0)

theorem add_lintegralIn (f g : SimpleFunc) {s : Set ℝ} (hs : MeasurableSet s) :
    (f + g).lintegralIn s = f.lintegralIn s + g.lintegralIn s := by
  calc
    (f + g).lintegralIn s = ∑ r ∈ f.range, (f + g).lintegralIn (f ⁻¹' {r} ∩ s) := by
      exact f.lintegralIn_partition (g := f + g) hs
    _ = ∑ r ∈ f.range, (SimpleFunc.const r + g).lintegralIn (f ⁻¹' {r} ∩ s) := by
      refine Finset.sum_congr rfl fun r hr ↦ ?_
      have hrs : MeasurableSet (f ⁻¹' {r} ∩ s) := (f.measurableSet_fiber r).inter hs
      rw [← restrict_lintegral _ hrs, ← restrict_lintegral _ hrs]
      refine congrArg SimpleFunc.lintegral ?_
      ext x
      by_cases hx : x ∈ f ⁻¹' {r} ∩ s
      · have hfx : f x = r := by simpa using hx.1
        simp [restrict_apply, hrs, hx, hfx]
      · simp [restrict_apply, hrs, hx]
    _ = ∑ r ∈ f.range,
          (r * measure (f ⁻¹' {r} ∩ s) + g.lintegralIn (f ⁻¹' {r} ∩ s)) := by
      refine Finset.sum_congr rfl fun r hr ↦ by
        have hrs : MeasurableSet (f ⁻¹' {r} ∩ s) := (f.measurableSet_fiber r).inter hs
        simpa using (g.const_add_lintegralIn r hrs)
    _ = (∑ r ∈ f.range, r * measure (f ⁻¹' {r} ∩ s)) +
          ∑ r ∈ f.range, g.lintegralIn (f ⁻¹' {r} ∩ s) := by
      rw [Finset.sum_add_distrib]
    _ = f.lintegralIn s + g.lintegralIn s := by
      rw [lintegralIn, g.lintegralIn_partition (f := f) hs]

theorem add_lintegral (f g : SimpleFunc) :
    (f + g).lintegral = f.lintegral + g.lintegral := by
  rw [(f + g).lintegral_eq_lintegralIn_univ, f.lintegral_eq_lintegralIn_univ,
    g.lintegral_eq_lintegralIn_univ]
  exact f.add_lintegralIn g MeasurableSet.univ

theorem lintegralIn_mono_fun {f g : SimpleFunc} {s : Set ℝ} (hs : MeasurableSet s) (hfg : f ≤ g) :
    f.lintegralIn s ≤ g.lintegralIn s := by
  calc
    f.lintegralIn s = ∑ r ∈ f.range, r * measure (f ⁻¹' {r} ∩ s) := rfl
    _ ≤ ∑ r ∈ f.range, g.lintegralIn (f ⁻¹' {r} ∩ s) := by
      refine Finset.sum_le_sum fun r hr ↦ ?_
      have hrs : MeasurableSet (f ⁻¹' {r} ∩ s) := (f.measurableSet_fiber r).inter hs
      calc
        r * measure (f ⁻¹' {r} ∩ s) =
            ∑ y ∈ g.range, r * measure (g ⁻¹' {y} ∩ (f ⁻¹' {r} ∩ s)) := by
              rw [← Finset.mul_sum, g.sum_range_measure_preimage_singleton_in hrs]
        _ ≤ ∑ y ∈ g.range, y * measure (g ⁻¹' {y} ∩ (f ⁻¹' {r} ∩ s)) := by
              refine Finset.sum_le_sum fun y hy ↦ ?_
              by_cases hμ : measure (g ⁻¹' {y} ∩ (f ⁻¹' {r} ∩ s)) = 0
              · simp [hμ]
              · rcases nonempty_of_measure_ne_zero hμ with ⟨x, hx⟩
                have hxg : g x = y := by simpa [inter_assoc] using hx.1
                have hxf : f x = r := by simpa [inter_assoc] using hx.2.1
                gcongr
                simpa [hxf, hxg] using hfg x
        _ = g.lintegralIn (f ⁻¹' {r} ∩ s) := by
              rfl
    _ = g.lintegralIn s := (g.lintegralIn_partition (f := f) hs).symm

theorem lintegral_mono_fun {f g : SimpleFunc} (hfg : f ≤ g) : f.lintegral ≤ g.lintegral :=
  by
    rw [f.lintegral_eq_lintegralIn_univ, g.lintegral_eq_lintegralIn_univ]
    exact lintegralIn_mono_fun MeasurableSet.univ hfg

end SimpleFunc

end Real

end MTI
