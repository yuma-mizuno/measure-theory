import Mathlib.Data.Set.Countable
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linter.Multigoal
import Mathlib.Tactic.FunProp.Attr
import Mathlib.Tactic.Measurability

set_option autoImplicit false

namespace MTI

open Set Encodable Function Equiv

variable {α β γ δ δ' : Type*} {ι : Sort*} {s t u : Set α}

/-- A measurable space is a space equipped with a σ-algebra. -/
@[class] structure MeasurableSpace (α : Type*) where
  /-- Predicate saying that a given set is measurable. Use `MeasurableSet` in the root namespace
  instead. -/
  MeasurableSet' : Set α → Prop
  /-- The empty set is a measurable set. Use `MeasurableSet.empty` instead. -/
  measurableSet_empty : MeasurableSet' ∅
  /-- The complement of a measurable set is a measurable set. Use `MeasurableSet.compl` instead. -/
  measurableSet_compl : ∀ s, MeasurableSet' s → MeasurableSet' sᶜ
  /-- The union of a sequence of measurable sets is a measurable set. Use a more general
  `MeasurableSet.iUnion` instead. -/
  measurableSet_iUnion : ∀ f : ℕ → Set α, (∀ i, MeasurableSet' (f i)) → MeasurableSet' (⋃ i, f i)

/-- `MeasurableSet s` means that `s` is measurable (in the ambient measure space on `α`) -/
def MeasurableSet [MeasurableSpace α] (s : Set α) : Prop :=
  ‹MeasurableSpace α›.MeasurableSet' s

scoped[MTI] notation "MeasurableSet[" m "]" => @MeasurableSet _ m

open MTI

section

open scoped symmDiff

@[simp, measurability]
theorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=
  MeasurableSpace.measurableSet_empty _

variable {m : MeasurableSpace α}

@[measurability]
protected theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet sᶜ :=
  MeasurableSpace.measurableSet_compl _ s

protected theorem MeasurableSet.of_compl (h : MeasurableSet sᶜ) : MeasurableSet s :=
  compl_compl s ▸ h.compl

@[simp]
theorem MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ MeasurableSet s :=
  ⟨.of_compl, .compl⟩

@[simp, measurability]
protected theorem MeasurableSet.univ : MeasurableSet (univ : Set α) :=
  .of_compl <| by simp

@[nontriviality, measurability]
theorem Subsingleton.measurableSet [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t := by
  rwa [← h]

@[measurability]
protected theorem MeasurableSet.iUnion [Countable ι] ⦃f : ι → Set α⦄
    (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) := by
  cases isEmpty_or_nonempty ι
  · simp
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iUnion_congr_of_surjective _ he (fun _ => rfl)]
    exact m.measurableSet_iUnion _ fun _ => h _

protected theorem MeasurableSet.biUnion {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) := by
  rw [biUnion_eq_iUnion]
  have := hs.to_subtype
  exact MeasurableSet.iUnion (by simpa using h)

theorem Set.Finite.measurableSet_biUnion {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  .biUnion hs.countable h

theorem Finset.measurableSet_biUnion {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biUnion h

protected theorem MeasurableSet.sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) := by
  rw [sUnion_eq_biUnion]
  exact .biUnion hs h

theorem Set.Finite.measurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs.countable h

@[measurability]
theorem MeasurableSet.iInter [Countable ι] {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋂ b, f b) :=
  .of_compl <| by rw [compl_iInter]; exact .iUnion fun b => (h b).compl

theorem MeasurableSet.biInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  .of_compl <| by rw [compl_iInter₂]; exact .biUnion hs fun b hb => (h b hb).compl

theorem Set.Finite.measurableSet_biInter {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  .biInter hs.countable h

theorem Finset.measurableSet_biInter {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biInter h

theorem MeasurableSet.sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋂₀ s) := by
  rw [sInter_eq_biInter]
  exact MeasurableSet.biInter hs h

theorem Set.Finite.measurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs.countable h

@[simp, measurability]
protected theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]
  exact .iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp, measurability]
protected theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∩ s₂) := by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl

@[simp, measurability]
protected theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl

@[simp, measurability]
protected lemma MeasurableSet.himp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ⇨ s₂) := by rw [himp_eq]; exact h₂.union h₁.compl

@[simp, measurability]
protected theorem MeasurableSet.symmDiff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∆ s₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp, measurability]
protected lemma MeasurableSet.bihimp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ⇔ s₂) := (h₂.himp h₁).inter (h₁.himp h₂)

@[simp, measurability]
protected theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t)
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diff ht)

open Classical in
theorem MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p → MeasurableSet s)
    (ht : ¬p → MeasurableSet t) : MeasurableSet (ite p s t) := by
  split_ifs with h
  exacts [hs h, ht h]

@[simp, measurability]
protected theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) {i : Bool} : MeasurableSet (cond i s₁ s₂) := by
  cases i
  exacts [h₂, h₁]

protected theorem MeasurableSet.const (p : Prop) : MeasurableSet { _a : α | p } := by
  by_cases p <;> simp [*]

protected lemma MeasurableSet.imp {p q : α → Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x → q x} := by
  have h_eq : {x | p x → q x} = {x | p x}ᶜ ∪ {x | q x} := by grind
  rw [h_eq]
  exact hs.compl.union ht

protected lemma MeasurableSet.iff {p q : α → Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x ↔ q x} := by
  have h_eq : {x | p x ↔ q x} = {x | p x → q x} ∩ {x | q x → p x} := by ext; simp; grind
  rw [h_eq]
  exact (hs.imp ht).inter (ht.imp hs)

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s ⊆ t ∧ MeasurableSet t } :=
  ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩

end

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive GenerateMeasurable (s : Set (Set α)) : Set α → Prop
  | basic : ∀ u ∈ s, GenerateMeasurable s u
  | empty : GenerateMeasurable s ∅
  | compl : ∀ t, GenerateMeasurable s t → GenerateMeasurable s tᶜ
  | iUnion : ∀ f : ℕ → Set α, (∀ n, GenerateMeasurable s (f n)) →
      GenerateMeasurable s (⋃ i, f i)

/-- Construct the smallest measure space containing a collection of basic sets -/
def generateFrom (s : Set (Set α)) : MeasurableSpace α where
  MeasurableSet' := GenerateMeasurable s
  measurableSet_empty := .empty
  measurableSet_compl := .compl
  measurableSet_iUnion := .iUnion

theorem measurableSet_generateFrom {s : Set (Set α)} {t : Set α} (ht : t ∈ s) :
    MeasurableSet[generateFrom s] t :=
  .basic t ht

@[elab_as_elim]
theorem generateFrom_induction [MeasurableSpace α] (C : Set (Set α)) (h_eq : ‹_› = generateFrom C)
    (p : ∀ s : Set α, MeasurableSet s → Prop) (hC : ∀ t ∈ C, ∀ ht, p t ht)
    (empty : p (∅ : Set α) (MeasurableSet.empty)) (compl : ∀ t ht, p t ht → p tᶜ ht.compl)
    (iUnion : ∀ (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)),
      (∀ n, p (s n) (hs n)) → p (⋃ i, s i) (.iUnion hs)) (s : Set α)
    (hs : MeasurableSet s) : p s hs := by
  rw [h_eq] at hs
  induction hs with
  | basic t ht => exact hC t ht hs
  | empty => exact empty
  | compl t ht ih => exact compl t (h_eq ▸ ht) (ih (h_eq ▸ ht))
  | iUnion f hf ih => exact iUnion f (h_eq ▸ hf) (fun n ↦ ih n (h_eq ▸ hf n))

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
@[fun_prop]
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @Measurable ..])
  (by fun_prop (disch := measurability))

set_option quotPrecheck false in
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Measurable[" m "]" => @Measurable _ _ m _
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain and codomain.
-/
scoped notation "Measurable[" mα ", " mβ "]" => @Measurable _ _ mα mβ

section MeasurableFunctions

theorem measurable_id {_ : MeasurableSpace α} : Measurable (@id α) := fun _ => id

@[fun_prop]
theorem measurable_id' {_ : MeasurableSpace α} : Measurable fun a : α => a := measurable_id

attribute [local push ←] Function.comp_def
@[to_fun]
protected theorem Measurable.comp {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) :=
  fun _ h => hf (hg h)

attribute [fun_prop] Measurable.fun_comp

@[simp, fun_prop]
theorem measurable_const {_ : MeasurableSpace α} {_ : MeasurableSpace β} {a : α} :
    Measurable fun _ : β => a := fun s _ => .const (a ∈ s)

end MeasurableFunctions

end MTI
