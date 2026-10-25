/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/Triangles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Real.Lemmas
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
