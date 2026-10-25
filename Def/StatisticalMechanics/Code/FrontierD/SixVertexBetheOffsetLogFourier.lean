/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourierLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogSingularity.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexRegularizedBetheLogNormDerivative
    (c epsilon x : Real) : Real :=
  let a := c ^ 2 - 1
  (-a * Real.sin x / (a ^ 2 + 1 + 2 * a * Real.cos x)) -
    Real.sin x / (2 - 2 * Real.cos x + epsilon)

end
end StatMech.FrontierD
