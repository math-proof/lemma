/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample
open Finset


namespace StatMech.FrontierD

def sixVertexFourByTwoReducedArrows
    (r : SixVertexFourByTwoReducedMask) :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v :=
    if v.2.val = 0 then
      if v.1.val = 0 then r 0 else if v.1.val = 2 then r 1 else false
    else
      if v.1.val = 1 then r 2 else if v.1.val = 3 then r 3 else false
  vertical v :=
    if v.2.val = 0 then
      if v.1.val = 1 then r 4 else if v.1.val = 3 then r 5 else false
    else
      if v.1.val = 0 then r 6 else if v.1.val = 2 then r 7 else false

def sixVertexFourByTwoVertex (x : Fin 4) (y : Fin 2) :
    sixVertexFourByTwoTorus.Vertex :=
  (⟨x.val, by change x.val < 4; exact x.isLt⟩,
    ⟨y.val, by change y.val < 2; exact y.isLt⟩)

def sixVertexFourByTwoReducedMaskOf
    (mask : SixVertexArrows sixVertexFourByTwoTorus) :
    SixVertexFourByTwoReducedMask :=
  fun i =>
    if i.val = 0 then mask.horizontal (sixVertexFourByTwoVertex 0 0)
    else if i.val = 1 then mask.horizontal (sixVertexFourByTwoVertex 2 0)
    else if i.val = 2 then mask.horizontal (sixVertexFourByTwoVertex 1 1)
    else if i.val = 3 then mask.horizontal (sixVertexFourByTwoVertex 3 1)
    else if i.val = 4 then mask.vertical (sixVertexFourByTwoVertex 1 0)
    else if i.val = 5 then mask.vertical (sixVertexFourByTwoVertex 3 0)
    else if i.val = 6 then mask.vertical (sixVertexFourByTwoVertex 0 1)
    else mask.vertical (sixVertexFourByTwoVertex 2 1)

end StatMech.FrontierD
