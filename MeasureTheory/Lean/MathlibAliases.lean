import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral

namespace MTI

@[inherit_doc _root_.MeasurableSpace]
abbrev MeasurableSpace := _root_.MeasurableSpace
@[inherit_doc _root_.MeasurableSet]
abbrev MeasurableSet {α} [MeasurableSpace α] (s : Set α) : Prop := _root_.MeasurableSet s
@[inherit_doc MeasureTheory.Measure]
abbrev Measure := MeasureTheory.Measure
@[inherit_doc _root_.Measurable]
abbrev Measurable {α β} [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  _root_.Measurable f
@[inherit_doc _root_.AEMeasurable]
abbrev AEMeasurable {α β} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  _root_.AEMeasurable f μ
@[inherit_doc MeasureTheory.SFinite]
abbrev SFinite {α} [MeasurableSpace α] (μ : Measure α) := MeasureTheory.SFinite μ
@[inherit_doc MeasureTheory.IsFiniteMeasure]
abbrev IsFiniteMeasure {α} [MeasurableSpace α] (μ : Measure α) := MeasureTheory.IsFiniteMeasure μ
@[inherit_doc Filter.Tendsto]
abbrev Tendsto {α β} (f : α → β) (l₁ : Filter α) (l₂ : Filter β) : Prop := Filter.Tendsto f l₁ l₂

end MTI
