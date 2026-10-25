/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceParticleHole
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUniformCentralPressure.Part3
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexCanonicalUniformHeightCentralTraceBound (q : Real) : Prop :=
  forall r k : Nat,
    SixVertexUniformHeightCentralTraceBound
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)

end
end StatMech.FrontierD
