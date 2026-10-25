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
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.Triangles
set_option maxHeartbeats 800000


noncomputable section

open Filter Topology Finset BigOperators

namespace RandomGraph

/-- The index of a pair with $a < b < n$ lies below $\binom{n}{2}$, ensuring that
`pairToEdgeIndex` produces a valid `Fin (Nat.choose n 2)`. -/
lemma pairToEdgeIndex_lt_choose {a b n : ℕ} (hab : a < b) (hbn : b < n) :
    pairToEdgeIndex a b < Nat.choose n 2 := by
  unfold pairToEdgeIndex
  have h1 : Nat.choose b 2 + a < Nat.choose b 2 + b := Nat.add_lt_add_left hab _
  have h2 : Nat.choose b 2 + b = Nat.choose (b + 1) 2 := by
    simp [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  rw [h2] at h1
  exact lt_of_lt_of_le h1 (Nat.choose_le_choose 2 hbn)

end RandomGraph
end
