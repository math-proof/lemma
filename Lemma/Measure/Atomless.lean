import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Measure.Atomless
open MeasureTheory Set Filter Topology
open MeasureTheory


/--
[isAtomless_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean)
-/
@[path]
private lemma isAtomless_restrict_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {Z : Set α}
-- given
  (hZ : MeasurableSet Z)
  (hA : IsAtomless μ) :
-- imply
  IsAtomless (μ.restrict Z) := by
-- proof
  apply MeasureTheory.isAtomless_restrict hZ hA

/--
[isAtomless_exists_subset_measure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean)
-/
@[path]
private lemma isAtomless_exists_subset_measure_eq_eq
  [MeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasure μ]
  {s : Set α}
  {t : ENNReal}
-- given
  (hA : IsAtomless μ)
  (hs : MeasurableSet s)
  (ht : t ≤ μ s) :
-- imply
  ∃ u, u ⊆ s ∧ MeasurableSet u ∧ μ u = t := by
-- proof
  apply MeasureTheory.isAtomless_exists_subset_measure_eq hA hs ht


-- created on 2026-10-20
