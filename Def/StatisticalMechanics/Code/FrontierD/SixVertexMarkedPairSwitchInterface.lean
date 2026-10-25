/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexMarkedSectorConfigurationPolynomial
    (T : EvenTorus) (n : Fin (T.width + 1)) : Real[X] :=
  ∑ omega : SixVertexMarkedSectorConfiguration T n,
    sixVertexTorusMarkedWeight omega.1

end
end StatMech.FrontierD
