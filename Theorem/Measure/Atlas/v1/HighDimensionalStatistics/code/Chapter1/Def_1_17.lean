module

public import Mathlib
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_17

public section

open Set Metric
open scoped NNReal


namespace IsEpsilonNet

/--
[empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_17.lean)
-/
public theorem empty
  [PseudoMetricSpace α]
  {K N : Set α}
  {ε : ℝ}
  {ε : ℝ} :
-- imply
  IsEpsilonNet (∅ : Set α) ∅ ε :=
-- proof
  ⟨Subset.rfl, fun _ hz => absurd hz (by simp)⟩

end IsEpsilonNet

namespace IsEpsilonNet

/--
[subset_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_17.lean)
-/
public theorem subset_set
  [PseudoMetricSpace α]
  {K N : Set α}
  {ε : ℝ}
-- given
  (h : IsEpsilonNet K N ε) :
-- imply
  N ⊆ K :=
-- proof
  h.1

end IsEpsilonNet

namespace IsEpsilonNet

/--
[exists_dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_17.lean)
-/
public theorem exists_dist_le
  [PseudoMetricSpace α]
  {K N : Set α}
  {ε : ℝ}
  {z : α}
-- given
  (h : IsEpsilonNet K N ε)
  (hz : z ∈ K) :
-- imply
  ∃ x ∈ N, dist x z ≤ ε :=
-- proof
  h.2 z hz

end IsEpsilonNet

namespace IsEpsilonNet

/--
[anti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_17.lean)
-/
public theorem anti
  [PseudoMetricSpace α]
  {K N : Set α}
  {ε : ℝ}
  {K' : Set α}
-- given
  (h : IsEpsilonNet K N ε)
  (hK' : K' ⊆ K)
  (hN : N ⊆ K') :
-- imply
  IsEpsilonNet K' N ε :=
-- proof
  ⟨hN, fun z hz => h.2 z (hK' hz)⟩

end IsEpsilonNet


-- created on 2026-10-23
