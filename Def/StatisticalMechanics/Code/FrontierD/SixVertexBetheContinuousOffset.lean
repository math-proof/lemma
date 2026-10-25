/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness


namespace StatMech.FrontierD

noncomputable section

def sixVertexContinuousOffsetSource (c x : Real) : Real :=
  (sixVertexTheta c x (-Real.pi) + sixVertexTheta c x Real.pi) / 2


def sixVertexContinuousOffsetKernel (c x y : Real) : Real :=
  sixVertexRootDensityKernel c x y / sixVertexRootDensityWeight c y

end
end StatMech.FrontierD
