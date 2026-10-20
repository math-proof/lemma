import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Function.Lusin
open MeasureTheory Measure Topology
open scoped ENNReal
open MathlibExt.MeasureTheory.Function.Lusin


/--
[lusin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Function/Lusin.lean)
-/
@[path]
private lemma lusin_eq
  [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [T2Space α] [LocallyCompactSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
  {μ : Measure α} [IsFiniteMeasure μ] [Regular μ]
  {f : α → β}
  {ε : ℝ}
-- given
  (hf : Measurable f)
  (hε : 0 < ε) :
-- imply
  ∃ K : Set α, IsCompact K ∧ μ (Kᶜ) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
-- proof
  apply MathlibExt.MeasureTheory.Function.Lusin.lusin hf hε


-- created on 2026-10-20
