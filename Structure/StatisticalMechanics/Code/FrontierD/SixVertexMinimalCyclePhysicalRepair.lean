/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part3


namespace StatMech.FrontierD

noncomputable section

structure SixVertexTwoLayerUnitCycleRepair
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat) where
  first : SixVertexDirectedSimpleCycle T
  second : SixVertexDirectedSimpleCycle T
  first_follows : first.Follows omega
  second_follows : second.Follows eta
  tail_disjoint : forall i j,
    (first.edge i).tail != (second.edge j).tail
  first_seam_flow :
    (∑ column : Fin T.width,
      first.verticalFlow (column, svFinLast T.height_pos)) = -1
  second_seam_flow :
    (∑ column : Fin T.width,
      second.verticalFlow (column, svFinLast T.height_pos)) = 1
  fine : sixVertexHorizontalPairBoundedFineRowProfile
      (omega.horizontal, eta.horizontal) =
    sixVertexHorizontalPairBoundedFineRowProfile
      ((sixVertexTorusFlip first.mask omega).horizontal,
        (sixVertexTorusFlip second.mask eta).horizontal)
  loopGrade_eq : loopGrade
      (sixVertexTorusFlip first.mask omega,
        sixVertexTorusFlip second.mask eta) = loopGrade (omega, eta)

end
end StatMech.FrontierD
