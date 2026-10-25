/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexLogOffsetQuotientLipschitzBound
    (c lower U G Lu D : Real) : Real :=
  (Lu * G + U * D) / lower +
    U * G * (sixVertexFiniteRootDensityLipschitzConstant c : Real) /
      lower ^ 2

def sixVertexLogOffsetQuotientLipschitzNNReal
    (c lower U G Lu D : Real) : NNReal :=
  Real.toNNReal
    (sixVertexLogOffsetQuotientLipschitzBound c lower U G Lu D)

end
end StatMech.FrontierD
