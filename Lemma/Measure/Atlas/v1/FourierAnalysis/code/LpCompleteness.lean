import Mathlib
import sympy.Basic
open MeasureTheory
open scoped ENNReal


namespace LpCompleteness

/--
[lp_banach_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/LpCompleteness.lean)
-/
@[path]
lemma lp_banach_space
  [MeasurableSpace X]
  {μ : Measure X}
  [NormedAddCommGroup E]
  [CompleteSpace E]
  {p : ℝ≥0∞}
  [hp : Fact (1 ≤ p)] :
-- imply
  CompleteSpace (Lp E p μ) :=
-- proof
  inferInstance

end LpCompleteness

namespace LpCompleteness

/--
[smooth_compactSupport_dense_Lp_Rn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/LpCompleteness.lean)
-/
@[path]
lemma smooth_compactSupport_dense_Lp_Rn
  {n : ℕ}
  {p : ℝ≥0∞}
  [hp : Fact (1 ≤ p)]
-- given
  (hp_top : p ≠ ⊤) :
-- imply
  Dense {f : Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin n))) | ∃ (g : EuclideanSpace ℝ (Fin n) → ℂ), f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g} :=
-- proof
  MeasureTheory.Lp.dense_hasCompactSupport_contDiff hp_top

end LpCompleteness


-- created on 2026-10-23
