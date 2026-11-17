/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Janson

@[expose] public section

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
