/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexOffsetCorrectionTerm
    (lam : Real) (n : Nat) (alpha : Real) : Real :=
  sixVertexGapCorrectionTerm lam n / Real.pi *
    Real.sin ((n + 1 : Real) * alpha)

end
end StatMech.FrontierD
