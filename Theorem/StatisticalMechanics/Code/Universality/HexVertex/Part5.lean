/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexVertex.Part4


namespace StatMech.Universality

open Complex


namespace VertexWalkData

variable (D : VertexWalkData)


theorem relation : D.vertexSum = 0 := by
  unfold vertexSum
  rw [Finset.sum_eq_zero (fun P _ => hexPairContribution_zero D.du (D.pairWind P) (D.pairLen P)),
      Finset.sum_eq_zero (fun T _ => hexTripletContribution_zero D.du (D.tripWind T) (D.tripLen T)),
      add_zero]

end VertexWalkData
end StatMech.Universality
