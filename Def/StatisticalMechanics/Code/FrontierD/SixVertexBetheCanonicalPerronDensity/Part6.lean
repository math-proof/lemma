/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part5
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalDensityPerronEmpiricalObservable
    {c : Real} (hc : 2 < c) (f : Real → Real) (k : Nat) : Real :=
  (∑ j, f (sixVertexCanonicalDensityPerronBetheRoots hc k j)) /
    (sixVertexFourWidth 0 k : Real)

end
end StatMech.FrontierD
