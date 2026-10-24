import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.RealAnalysis.code.Sequences.Basic
open Sequences


namespace Sequences

/--
[seq_converges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Basic.lean)
-/
@[path]
lemma seq_converges_iff
  {x : ℕ → ℝ}
  {L : ℝ} :
-- imply
  Filter.Tendsto x Filter.atTop (nhds L) ↔ ∀ ε > 0, ∃ M : ℕ, ∀ n ≥ M, := by
-- proof
  rw [Metric.tendsto_atTop]
  simp_rw [Real.dist_eq]

end Sequences

namespace Sequences

/--
[squeeze_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Basic.lean)
-/
@[path]
lemma squeeze_theorem
  {a x b : ℕ → ℝ}
  {L : ℝ}
-- given
  (hab : ∀ n, a n ≤ x n)
  (hxb : ∀ n, x n ≤ b n)
  (ha : Filter.Tendsto a Filter.atTop (nhds L))
  (hb : Filter.Tendsto b Filter.atTop (nhds L)) :
-- imply
  Filter.Tendsto x Filter.atTop (nhds L) :=
-- proof
  tendsto_of_tendsto_of_tendsto_of_le_of_le ha hb hab hxb

end Sequences


-- created on 2026-10-23
