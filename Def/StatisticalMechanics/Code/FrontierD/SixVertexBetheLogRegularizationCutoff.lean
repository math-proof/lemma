/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogBulk.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalEvenOffsetLinear.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexBetheLogRegularizationError
    (c epsilon x : Real) : Real :=
  sixVertexBetheLogNormKernel c x -
    sixVertexRegularizedBetheLogKernel c epsilon x

end
end StatMech.FrontierD
