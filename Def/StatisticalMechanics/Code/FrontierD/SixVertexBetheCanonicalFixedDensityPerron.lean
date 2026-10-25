/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

noncomputable def sixVertexCanonicalFixedEvenDensityFloor
    {c : Real} (hc : 2 < c) (s : Nat) : Real :=
  Classical.choose
    (eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor
      hc s)

end
end StatMech.FrontierD
