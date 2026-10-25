/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexBoundary.Part2


namespace StatMech.Universality

open Complex Filter Topology

open scoped Topology Real BigOperators


namespace HexDomain

variable {V : Type*} [DecidableEq V] (D : HexDomain V)


omit [DecidableEq V] in


theorem globalSum_eq_zero : D.globalSum = 0 := by
  unfold globalSum
  apply Finset.sum_eq_zero
  intro v hv
  have h := D.relation v hv
  simpa [incTerm] using h

end HexDomain
end StatMech.Universality
