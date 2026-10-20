import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.FunctionalAnalysis.DunfordPettis
open MeasureTheory
open scoped ENNReal
open scoped Pointwise
open Filter Topology
open MathlibExt.Analysis.FunctionalAnalysis.DunfordPettisWanted


/--
[dunford_pettis_compactness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/DunfordPettis.lean)
-/
@[path]
private lemma dunford_pettis_compactness_eq
  [MeasurableSpace α]
  {μ : Measure α} [IsFiniteMeasure μ]
  {f : ι → α → ℝ}
-- given
  (hf : ∀ i, MemLp (f i) 1 μ) :
-- imply
  UniformIntegrable f (1 : ℝ≥0∞) μ ↔
    IsCompact
    (closure
    (toWeakSpace ℝ (Lp ℝ 1 μ) '' Set.range (fun i => (hf i).toLp (f i))
    : Set (WeakSpace ℝ (Lp ℝ 1 μ)))) := by
-- proof
  apply MathlibExt.Analysis.FunctionalAnalysis.DunfordPettisWanted.dunford_pettis_compactness f hf


-- created on 2026-10-20
