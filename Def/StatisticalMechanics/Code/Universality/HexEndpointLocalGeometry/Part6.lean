/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part7


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

noncomputable def HexEndpointLocalCrossing.loopCoord
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (i : Fin C.loopLength) : HexAWCoord :=
  hexEndpointPrefixCoord ts hlegal (C.index + i.val)


noncomputable def HexEndpointLocalCrossing.loopCoords
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) : List HexAWCoord :=
  List.ofFn (C.loopCoord hlegal)

end
end StatMech.Universality
