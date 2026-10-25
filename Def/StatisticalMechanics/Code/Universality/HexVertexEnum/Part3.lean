/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexEnum.Part4


namespace StatMech.Universality

open Complex

open HexWalk


namespace HexVertexEnumeration

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


noncomputable def toVertexWalkData (E : HexVertexEnumeration region a h0 v du) :
    VertexWalkData where
  du := du
  pairs := E.pairs
  pairWind := fun P => (ofTurns a h0 (E.pairBase P)).turnCount
  pairLen := fun P => (ofTurns a h0 (E.pairBase P ++ E.pairLq P)).numVertices
  triplets := E.triplets
  tripWind := fun T => (ofTurns a h0 (E.tripBase T)).turnCount
  tripLen := fun T => (ofTurns a h0 (E.tripBase T)).numVertices


end HexVertexEnumeration
end StatMech.Universality
