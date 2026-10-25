/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingSubgroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectWindingSubgroupRankTwo_iff_of_reachable
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R omega).Reachable x y) :
    FKRectWindingSubgroupRankTwo R omega x ↔
      FKRectWindingSubgroupRankTwo R omega y := by
  rw [FKRectWindingSubgroupRankTwo, FKRectWindingSubgroupRankTwo,
    fkRectClosedWindingSubgroup_eq_of_reachable R omega hxy]


theorem fkRectHasNet_iff_exists_windingSubgroup_rankTwo
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectHasNet R omega ↔
      ∃ x : R.Vertex, FKRectWindingSubgroupRankTwo R omega x := by
  constructor
  · rintro ⟨x, p, q, hpq⟩
    exact ⟨x, fkRectWalkWinding R p, ⟨p, rfl⟩,
      fkRectWalkWinding R q, ⟨q, rfl⟩, hpq⟩
  · rintro ⟨x, u, ⟨p, hp⟩, v, ⟨q, hq⟩, huv⟩
    refine ⟨x, p, q, ?_⟩
    simpa [hp, hq] using huv


theorem fkRectNetIndicator_eq_one_iff_exists_windingSubgroup_rankTwo
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectNetIndicator R omega = 1 ↔
      ∃ x : R.Vertex, FKRectWindingSubgroupRankTwo R omega x := by
  rw [fkRectNetIndicator_eq_one_iff,
    fkRectHasNet_iff_exists_windingSubgroup_rankTwo]

end
end StatMech.FrontierD
