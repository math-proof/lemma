/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexGapEulerLogs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapLambertProduct
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDualGapAsymptotic.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexGapEulerLogs
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexAlternatingPlusEulerLog (t : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * Real.log
    (1 + Real.exp (-2 * Real.pi * t * (n + 1 : ℝ)))

end
end StatMech.FrontierD
