/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexRegularizedBetheLogLipschitzConstant
    (c epsilon : Real) : NNReal :=
  Real.toNNReal ((1 / 2 : Real) *
    ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2 + 2 / epsilon))


end
end StatMech.FrontierD
