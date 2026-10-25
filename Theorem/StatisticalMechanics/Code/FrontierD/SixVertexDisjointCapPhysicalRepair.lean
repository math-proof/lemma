/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part2


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexDisjointCapUnitRepair

theorem target_ice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade)
    (homega : omega.IceRule) (heta : eta.IceRule) :
    repair.target.1.IceRule ∧ repair.target.2.IceRule := by
  exact ⟨repair.first.cycle.flip_ice omega homega
      repair.first.cycle_follows,
    repair.second.cycle.flip_ice eta heta
      repair.second.cycle_follows⟩


theorem first_upCount
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    (sixVertexUpCount
        (svTorusVerticalRows T repair.target.1
          (svFinLast T.height_pos)) : Int) =
    (sixVertexUpCount
        (svTorusVerticalRows T omega
          (svFinLast T.height_pos)) : Int) + 1 := by
  change
    (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusFlip repair.first.cycle.mask omega)
          (svFinLast T.height_pos)) : Int) = _
  rw [sixVertexTorusFlip_upCount,
    repair.first.cycle.flip_seamDelta omega
      repair.first.cycle_follows,
    repair.first_seam_flow]
  norm_num


theorem second_upCount
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    (sixVertexUpCount
        (svTorusVerticalRows T repair.target.2
          (svFinLast T.height_pos)) : Int) =
    (sixVertexUpCount
        (svTorusVerticalRows T eta
          (svFinLast T.height_pos)) : Int) - 1 := by
  change
    (sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexTorusFlip repair.second.cycle.mask eta)
          (svFinLast T.height_pos)) : Int) = _
  rw [sixVertexTorusFlip_upCount,
    repair.second.cycle.flip_seamDelta eta
      repair.second.cycle_follows,
    repair.second_seam_flow]
  ring


theorem target_twoCycleFine
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    sixVertexPairAtMostTwoCycleFineRelated (omega, eta) repair.target := by
  refine ⟨sixVertexDirectedSimpleCycles_flip_pair_related
      repair.first.cycle repair.second.cycle omega eta
      repair.first.cycle_follows repair.second.cycle_follows
      repair.cycle_tail_disjoint, repair.fine⟩

end SixVertexDisjointCapUnitRepair
end
end StatMech.FrontierD
