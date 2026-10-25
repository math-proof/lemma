/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexTwoLayerUnitCycleRepair

theorem target_ice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade)
    (homega : omega.IceRule) (heta : eta.IceRule) :
    repair.target.1.IceRule ∧ repair.target.2.IceRule :=
  ⟨repair.first.flip_ice omega homega repair.first_follows,
    repair.second.flip_ice eta heta repair.second_follows⟩

theorem first_upCount
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade) :
    (sixVertexUpCount
        (svTorusVerticalRows T repair.target.1
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T omega
          (svFinLast T.height_pos)) : Int) + 1 := by
  change
    (sixVertexUpCount
        (svTorusVerticalRows T (sixVertexTorusFlip repair.first.mask omega)
          (svFinLast T.height_pos)) : Int) = _
  rw [sixVertexTorusFlip_upCount,
    repair.first.flip_seamDelta omega repair.first_follows,
    repair.first_seam_flow]
  norm_num

theorem second_upCount
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade) :
    (sixVertexUpCount
        (svTorusVerticalRows T repair.target.2
          (svFinLast T.height_pos)) : Int) =
      (sixVertexUpCount
        (svTorusVerticalRows T eta
          (svFinLast T.height_pos)) : Int) - 1 := by
  change
    (sixVertexUpCount
        (svTorusVerticalRows T (sixVertexTorusFlip repair.second.mask eta)
          (svFinLast T.height_pos)) : Int) = _
  rw [sixVertexTorusFlip_upCount,
    repair.second.flip_seamDelta eta repair.second_follows,
    repair.second_seam_flow]
  ring

theorem target_twoCycleFine
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade) :
    sixVertexPairAtMostTwoCycleFineRelated (omega, eta) repair.target :=
  ⟨sixVertexDirectedSimpleCycles_flip_pair_related
      repair.first repair.second omega eta repair.first_follows
      repair.second_follows repair.tail_disjoint,
    repair.fine⟩

end SixVertexTwoLayerUnitCycleRepair
end
end StatMech.FrontierD
