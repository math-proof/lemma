/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/Triangles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

set_option maxHeartbeats 800000


noncomputable section

open Filter Topology Finset BigOperators

namespace RandomGraph

/-- Linear index assigned to an unordered pair $\{a, b\}$ with $a < b$, given by
$\binom{b}{2} + a$. Used to enumerate edges of the complete graph $K_n$ as
elements of $\mathrm{Fin}\binom{n}{2}$. -/
def pairToEdgeIndex (a b : ℕ) : ℕ := Nat.choose b 2 + a

end RandomGraph
end
