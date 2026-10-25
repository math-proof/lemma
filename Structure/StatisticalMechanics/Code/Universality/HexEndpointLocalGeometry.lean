/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

structure HexEndpointLocalCrossing (ts : List ℤ) (c : HexAWCoord) where
  index : ℕ
  index_lt : index < ts.length
  before : Fin 3
  after : Fin 3
  before_ne_after : before ≠ after
  before_mid : hexInfra_midAccum hexAWStart 1 (ts.take index) =
    hexAWMid c before
  at_vertex : hexInfra_midAccum hexAWStart 1 (ts.take index) +
    halfStep (hexInfra_headAccum 1 (ts.take index)) = hexAWPos c
  after_mid : hexInfra_midAccum hexAWStart 1 (ts.take (index + 1)) =
    hexAWMid c after


end
end StatMech.Universality
