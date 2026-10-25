/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogInterface


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def SixVertexCanonicalOddZeroModeWallisLimit
    {c : Real} (hc : 2 < c) (s : Nat) : Prop :=
  Tendsto (sixVertexCanonicalOddZeroModeWallisCorrection hc s) atTop
    (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c))))


end
end StatMech.FrontierD
