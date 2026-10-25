/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset


namespace StatMech.FrontierD

noncomputable section

def SixVertexSatisfiesContinuousOffsetEquation
    (c : Real) (tau : Real → Real) : Prop :=
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
    2 * Real.pi * tau x = sixVertexContinuousOffsetSource c x -
      ∫ y in -Real.pi..Real.pi,
        sixVertexContinuousOffsetKernel c x y * tau y

end
end StatMech.FrontierD
