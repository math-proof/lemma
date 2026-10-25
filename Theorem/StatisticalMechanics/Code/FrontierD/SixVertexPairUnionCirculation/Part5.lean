/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCirculation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCirculation.Part5


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPlaquetteBoundaryCirculation_isCirculation
    {T : EvenTorus} (cell : T.Vertex) (coefficient : Int) :
    SixVertexTorusCirculation T
      (sixVertexPlaquetteBoundaryCirculation cell coefficient).1
      (sixVertexPlaquetteBoundaryCirculation cell coefficient).2 := by
  intro v
  have hx :
      SixVertexArrows.cyclicPred T.width_pos v.1 = cell.1 ↔
        v.1 = finitePeriodicSucc T.width_pos cell.1 := by
    constructor
    · intro h
      rw [← finitePeriodicSucc_cyclicPred T.width_pos v.1, h]
    · intro h
      rw [h, svCyclicPred_finitePeriodicSucc]
  have hy :
      SixVertexArrows.cyclicPred T.height_pos v.2 = cell.2 ↔
        v.2 = finitePeriodicSucc T.height_pos cell.2 := by
    constructor
    · intro h
      rw [← finitePeriodicSucc_cyclicPred T.height_pos v.2, h]
    · intro h
      rw [h, svCyclicPred_finitePeriodicSucc]
  unfold sixVertexPlaquetteBoundaryCirculation
  by_cases hvx : v.1 = cell.1 <;>
    by_cases hvxSucc :
      v.1 = finitePeriodicSucc T.width_pos cell.1 <;>
    by_cases hvy : v.2 = cell.2 <;>
    by_cases hvySucc :
      v.2 = finitePeriodicSucc T.height_pos cell.2 <;>
    simp_all [Prod.ext_iff]

theorem sixVertexTorusCirculation_sum
    {T : EvenTorus} {Index : Type*} [Fintype Index]
    (horizontal vertical : Index -> T.Vertex -> Int)
    (hcirculation : forall index,
      SixVertexTorusCirculation T (horizontal index) (vertical index)) :
    SixVertexTorusCirculation T
      (fun v => ∑ index, horizontal index v)
      (fun v => ∑ index, vertical index v) := by
  intro v
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index hindex
  exact hcirculation index v


end
end StatMech.FrontierD
