import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter3.RandomGreedyColoring.StructuralLemma
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter3.RandomGreedyColoring.StructuralLemma
open Finset Fintype


namespace TwoColorableHypergraph

/--
[one_eighth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/RandomGreedyColoring/Theorem351.lean)
-/
@[path]
lemma one_eighth_bound
  [Fintype V]
  [DecidableEq V]
  {k : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  (1 : ℝ) / 8 * (1 + 1 / Real.log ↑k) < 1 := by
-- proof
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogk : Real.log 2 ≤ Real.log (↑k : ℝ) := by
    apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
    exact_mod_cast hk
  have hlogk_pos : (0 : ℝ) < Real.log ↑k := by linarith
  have hlogk_bound : (0.6931471803 : ℝ) < Real.log ↑k := by linarith
  have h1 : 1 / Real.log ↑k < 1 / 0.6931471803 := by
    apply div_lt_div_of_pos_left one_pos (by positivity) hlogk_bound
  have h2 : (1:ℝ) / 0.6931471803 < 1.4428 := by norm_num
  linarith
/-- Probabilistic existence statement: for $k$-uniform hypergraphs with at most
$c \sqrt{k/\log k} \, 2^k$ edges (with $0 < c \leq 1/8$), some injective ordering of the
vertices yields no conflicting pair. -/

end TwoColorableHypergraph


-- created on 2026-10-23
