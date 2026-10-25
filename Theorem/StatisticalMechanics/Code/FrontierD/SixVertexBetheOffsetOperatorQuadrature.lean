/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetOperatorQuadrature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargePeriodicQuadrature
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTaylor
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset.Part2


namespace StatMech.FrontierD

noncomputable section

theorem periodic_sixVertexRootDensityWeight (c : Real) :
    Function.Periodic (sixVertexRootDensityWeight c) (2 * Real.pi) := by
  intro x
  unfold sixVertexRootDensityWeight
  rw [sixVertexBetheIntegratingFactor_add_two_pi]

theorem periodic_sixVertexContinuousOffsetKernel_right (c x : Real) :
    Function.Periodic (sixVertexContinuousOffsetKernel c x)
      (2 * Real.pi) :=
  (periodic_sixVertexRootDensityKernel_right c x).div
    (periodic_sixVertexRootDensityWeight c)

end
end StatMech.FrontierD
