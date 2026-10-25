/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open scoped BigOperators
open SimpleGraph


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem openSub_mono {a b : ConfigSpace (Sym2 V)} (hab : a ≤ b) :
    openSub G a ≤ openSub G b := by
  intro x y h
  refine ⟨h.1, ?_⟩
  have hle := hab s(x, y)
  rw [h.2] at hle
  exact le_antisymm (Bool.le_true _) hle


end FK
end StatMech
