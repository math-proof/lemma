/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierKernelClosedForm
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityMomentum.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexRapidityMomentum (lam alpha : Real) : Real :=
  ∫ t in (0 : Real)..alpha, sixVertexXiFourier lam t

end
end StatMech.FrontierD
