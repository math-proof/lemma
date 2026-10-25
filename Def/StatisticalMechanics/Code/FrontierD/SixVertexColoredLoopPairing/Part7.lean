/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part9


namespace StatMech.FrontierD

noncomputable section

def fkColoredLocalPairCross
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  ({ pairing := pair.1.pairing, west := pair.1.west, east := pair.2.east },
   { pairing := pair.2.pairing, west := pair.2.west, east := pair.1.east })


def fkColoredLocalPairCrossWest
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  ({ pairing := pair.1.pairing, west := pair.2.west, east := pair.1.east },
   { pairing := pair.2.pairing, west := pair.1.west, east := pair.2.east })


def fkColoredLocalPairReconnection
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  ({ pairing := pair.1.pairing, west := pair.2.west, east := pair.2.east },
   { pairing := pair.2.pairing, west := pair.1.west, east := pair.1.east })


def fkColoredLocalPairOddCross
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  if pair.1.west != pair.2.west then fkColoredLocalPairCrossWest pair
  else fkColoredLocalPairCross pair

end
end StatMech.FrontierD
