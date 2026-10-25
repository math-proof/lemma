/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairFractionalTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexMarkedConfigurationPairMass
    {T : EvenTorus} (k : Nat)
    (pair : SixVertexArrows T × SixVertexArrows T) : Real :=
  sixVertexMarkedPairMultiplicity pair.1 pair.2 k


end
end StatMech.FrontierD
