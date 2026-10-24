/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/MeasureTheory/Integral/LyapunovConvexity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import sympy.atlas.MeasureTheory.Integral.LyapunovConvexity
import Lemma.Measure.Integral.LyapunovConvexity
import Lemma.Measure.Atomless
import sympy.atlas.MeasureTheory.Measure.Atomless
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open MathlibExt.MeasureTheory.Integral.LyapunovConvexityWanted

/-- Restriction preserves atomlessness with no finiteness hypothesis. -/
example {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hA : IsAtomless μ) {Z : Set α} (hZ : MeasurableSet Z) :
    IsAtomless (μ.restrict Z) :=
  isAtomless_restrict hZ hA

/-- Restriction of infinite Lebesgue measure on `ℝ` stays atomless. -/
example (hA : IsAtomless (volume : Measure ℝ)) {Z : Set ℝ}
    (hZ : MeasurableSet Z) :
    IsAtomless ((volume : Measure ℝ).restrict Z) :=
  isAtomless_restrict hZ hA

/-- Boundary case `t = 0` of the exact-subset-measure theorem. -/
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (hA : IsAtomless μ) {s : Set α} (hs : MeasurableSet s) :
    ∃ u, u ⊆ s ∧ MeasurableSet u ∧ μ u = 0 :=
  isAtomless_exists_subset_measure_eq hA hs zero_le

/-- Boundary case `t = μ s` of the exact-subset-measure theorem. -/
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (hA : IsAtomless μ) {s : Set α} (hs : MeasurableSet s) :
    ∃ u, u ⊆ s ∧ MeasurableSet u ∧ μ u = μ s :=
  isAtomless_exists_subset_measure_eq hA hs le_rfl

/-- Simple use of the full Lyapunov convexity theorem. -/
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : α → E) (hf : Integrable f μ) (hA : IsAtomless μ) :
    IsCompact (lyapunovRange μ f) ∧ Convex ℝ (lyapunovRange μ f) :=
  lyapunov_convexity f hf hA
