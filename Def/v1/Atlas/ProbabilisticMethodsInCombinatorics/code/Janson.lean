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
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Janson
set_option maxHeartbeats 800000

open Filter Real
open scoped Topology


noncomputable section

namespace Janson

/-- Probability that the $i$-th bad event $A_i$ occurs, i.e.
$\mathbb{P}(A_i) = \prod_{j \in S_i} p_j$. -/
def JansonSetup.probEvent (J : JansonSetup) (i : Fin J.k) : ℝ :=
  ∏ j ∈ J.S i, J.prob j

/-- The expected number of bad events, $\mu = \sum_{i=1}^{k} \mathbb{P}(A_i)$. -/
def JansonSetup.mu (J : JansonSetup) : ℝ :=
  ∑ i : Fin J.k, J.probEvent i

/-- Dependency relation between bad events: events $A_i$ and $A_j$ are dependent iff
$i \ne j$ and $S_i \cap S_j \ne \emptyset$. -/
def JansonSetup.dep (J : JansonSetup) (i j : Fin J.k) : Prop :=
  i ≠ j ∧ (J.S i ∩ J.S j).Nonempty

end Janson
end
