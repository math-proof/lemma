/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalCoordinate
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness


namespace StatMech.FrontierD

noncomputable section

theorem neg_pi_le_pi : -Real.pi <= Real.pi := by
  linarith [Real.pi_pos]


end
end StatMech.FrontierD
