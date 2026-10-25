/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexMarkedPairMultiplicity
    {T : EvenTorus} (omega eta : SixVertexArrows T) (k : Nat) : Real :=
  (sixVertexTorusMarkedWeight omega *
    sixVertexTorusMarkedWeight eta).coeff k


noncomputable def sixVertexMarkedSectorPairMass
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) : Real :=
  ∑ pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right,
    sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k

end
end StatMech.FrontierD
