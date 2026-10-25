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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem sixVertexCanonicalFixedEvenDensityFloor_pos
    {c : Real} (hc : 2 < c) (s : Nat) :
    0 < sixVertexCanonicalFixedEvenDensityFloor hc s :=
  (Classical.choose_spec
    (eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor
      hc s)).1

end
end StatMech.FrontierD
