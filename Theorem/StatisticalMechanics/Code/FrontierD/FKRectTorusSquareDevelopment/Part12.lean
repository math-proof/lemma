/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part11


namespace StatMech.FrontierD

noncomputable section

theorem fkRectHasSquareLiftNet_iff
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectHasSquareLiftNet R omega ↔ FKRectHasNet R omega := by
  constructor
  · rintro ⟨x, w, z, p, q, a, b, hw, hz, hind⟩
    exact ⟨x, w, z,
      (hw.closed_developedIndependent_iff R hz).mp hind⟩
  · rintro ⟨x, w, z, hind⟩
    let p : Int × Int := ((x.1.val : Int), (x.2.val : Int))
    have hp : fkRectLiftedVertex R p = x := by
      apply Prod.ext <;>
        simp [p, fkRectLiftedVertex]
    obtain ⟨q, hw⟩ := fkRectWalk_exists_squareLift R
      (fkRectOpenGraph_le_torusGraph R omega) w p hp
    obtain ⟨b, hz⟩ := fkRectWalk_exists_squareLift R
      (fkRectOpenGraph_le_torusGraph R omega) z p hp
    exact ⟨x, w, z, p, q, p, b, hw, hz,
      (hw.closed_developedIndependent_iff R hz).mpr hind⟩

end
end StatMech.FrontierD
