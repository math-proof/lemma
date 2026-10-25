/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part2


namespace StatMech.FrontierD

noncomputable section

def fkLayeredLoopColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (x : FKLayeredMedialDart T) : Bool :=
  (source x.1).color x.2

def fkLayeredBondMate
    (T : EvenTorus) (x : FKLayeredMedialDart T) :
    FKLayeredMedialDart T :=
  (x.1, fkMedialBondMate T x.2)


def fkColoredVertexCrossRawColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool) (x : FKLayeredMedialDart T) : Bool :=
  let localPair :=
    ((source false).localPairing x.2.1,
      (source true).localPairing x.2.1)
  let crossed := fkColoredLocalPairCrossIf (mask x.2.1) localPair
  (if x.1 then crossed.2 else crossed.1).sideColor x.2.2

end
end StatMech.FrontierD
