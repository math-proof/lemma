/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset.Part2


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexContinuousOffsetResidual
    (c : Real) (f : Real → Real) (x : Real) : Real :=
  2 * Real.pi * f x - sixVertexContinuousOffsetSource c x +
    ∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c x y * f y

end
end StatMech.FrontierD
