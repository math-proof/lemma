/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexRegularizedBetheLogNormDerivativeBound
    (c epsilon : Real) : Real :=
  (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2 + 1 / epsilon

end
end StatMech.FrontierD
