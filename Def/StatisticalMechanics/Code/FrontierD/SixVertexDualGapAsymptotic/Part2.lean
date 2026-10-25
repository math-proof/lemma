/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDualGapAsymptotic
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

def sixVertexDualGapRate (lam : Real) : Real :=
  sixVertexDualGapPowerSeries (Real.exp (-(Real.pi ^ 2) / (2 * lam)))


end
end StatMech.FrontierD
