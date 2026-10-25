/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEulerDefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

def fkRectMedialLoopCount (R : FKRectTorus)
    (omega : R.Configuration) : Nat :=
  fkMedialLoopCount R.medialTorus
    (fkRectConfigurationToMedialPairing R omega)


def fkRectEulerHomologyDefect (R : FKRectTorus)
    (omega : R.Configuration) : Int :=
  2 * (fkRectNumClusters R omega : Int) +
      (fkRectOpenEdgeCount R omega : Int) -
    (fkRectMedialLoopCount R omega : Int) -
    (R.width * R.height : Nat)

end
end StatMech.FrontierD
