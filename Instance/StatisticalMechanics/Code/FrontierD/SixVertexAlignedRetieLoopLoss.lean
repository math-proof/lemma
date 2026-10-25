/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedRetieLoopLoss


namespace StatMech.FrontierD

namespace FourByTwoAlignedRetieLoopLoss

instance (arrows : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable arrows.IceRule :=
  inferInstanceAs (Decidable (forall v, arrows.incomingCount v = 2))

instance (first second : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable (SixVertexLocallyDegreeTwo first second) := by
  unfold SixVertexLocallyDegreeTwo
  infer_instance

instance (pairing : Bool)
    (arrows : SixVertexArrows sixVertexFourByTwoTorus)
    (v : sixVertexFourByTwoTorus.Vertex) :
    Decidable (fkLoopPairingCompatible pairing arrows v) := by
  unfold fkLoopPairingCompatible
  infer_instance

end FourByTwoAlignedRetieLoopLoss
end StatMech.FrontierD
