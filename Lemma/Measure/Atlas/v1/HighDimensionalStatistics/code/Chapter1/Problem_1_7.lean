import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Problem_1_7
open Set Metric IsEpsilonSeparated
open scoped NNReal ENNReal


namespace IsEpsilonSeparated

/--
[subset_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_7.lean)
-/
@[path]
lemma subset_set
  [PseudoMetricSpace α]
  {K S : Set α}
  {ε : ℝ}
-- given
  (h : IsEpsilonSeparated K S ε) :
-- imply
  S ⊆ K :=
-- proof
  h.1

end IsEpsilonSeparated

namespace IsEpsilonSeparated

/--
[empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_7.lean)
-/
@[path]
lemma empty
  [PseudoMetricSpace α]
  {K S : Set α}
  {ε : ℝ}
  {K : Set α}
  {ε : ℝ} :
-- imply
  IsEpsilonSeparated K ∅ ε :=
-- proof
  ⟨empty_subset K, pairwise_empty _⟩

end IsEpsilonSeparated


-- created on 2026-10-23
