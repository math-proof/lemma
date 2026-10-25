/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
set_option maxHeartbeats 800000

open Filter Real
open scoped Topology


noncomputable section

namespace Janson

/-- A Janson setup consists of $N$ independent Bernoulli variables with success probabilities
`prob i ∈ [0,1]` and a family of $k$ "bad events" indexed by subsets $S_i \subseteq \{0,\dots,N-1\}$,
where event $i$ occurs iff every coordinate in $S_i$ is present in the random subset. -/
structure JansonSetup where
  N : ℕ
  k : ℕ
  prob : Fin N → ℝ
  S : Fin k → Finset (Fin N)
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_le_one : ∀ i, prob i ≤ 1

end Janson
end
