import Mathlib
import sympy.Basic
import sympy.atlas.Probability.CramerWold
open MeasureTheory ProbabilityTheory
open scoped Topology
open MathlibExt.Probability.CramerWoldWanted


/--
[cramer_wold_device](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/CramerWold.lean)
-/
@[path]
private lemma cramer_wold_device_eq
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {d : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : ℕ → Ω → EuclideanSpace ℝ (Fin d)}
  {Z : Ω' → EuclideanSpace ℝ (Fin d)}
-- given
  (h : ∀ t : EuclideanSpace ℝ (Fin d), TendstoInDistribution (fun n (ω : Ω) => @inner ℝ (EuclideanSpace ℝ (Fin d)) _ t (X n ω)) Filter.atTop (fun ω' => @inner ℝ (EuclideanSpace ℝ (Fin d)) _ t (Z ω')) (fun _ => μ) μ') :
-- imply
  TendstoInDistribution X Filter.atTop Z (fun _ => μ) μ' := by
-- proof
  apply MathlibExt.Probability.CramerWoldWanted.cramer_wold_device X Z h


-- created on 2026-10-20
