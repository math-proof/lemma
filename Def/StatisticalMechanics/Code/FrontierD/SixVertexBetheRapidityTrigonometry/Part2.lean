/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityMomentum.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityTrigonometry


namespace StatMech.FrontierD

noncomputable section

def sixVertexCircleRatio (lam alpha : Real) : Complex :=
  sixVertexMomentumCircle lam alpha / sixVertexRapidityCircle lam alpha

end
end StatMech.FrontierD
