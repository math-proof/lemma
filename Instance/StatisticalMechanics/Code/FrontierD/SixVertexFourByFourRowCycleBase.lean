/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11


namespace StatMech.FrontierD

noncomputable section

instance svHorizontalIceDecidable
    {N : Nat} (hN : 0 < N) (x y horizontal : SixVertexRow N) :
    Decidable (svHorizontalIce hN x y horizontal) :=
  inferInstanceAs (Decidable (∀ i,
    svHorizontalIncomingCount hN x y horizontal i = 2))

instance computableNatDecidableEq : DecidableEq Nat := Nat.decEq

end
end StatMech.FrontierD
