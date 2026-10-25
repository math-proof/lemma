/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part4


namespace StatMech.FrontierD

noncomputable section

theorem canonicalPhysicalPairedBranches_of_unitCyclePairedRepairs
    (hrepairs : SixVertexCanonicalPositiveEvenTraceUnitCyclePairedRepairs) :
    SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches := by
  intro r k M n hn0 hnN
  obtain ⟨repairs⟩ := hrepairs r k M n hn0 hnN
  exact ⟨repairs.toPhysicalPairedBranches⟩


theorem
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_unitCyclePairedRepairs
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale → Even scale →
      12 * scale + 2 < 2 * (k + 3) →
      ∀ᶠ blocks in Filter.atTop,
        hardFloor ≤
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hrepairs : SixVertexCanonicalPositiveEvenTraceUnitCyclePairedRepairs) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) :=
  fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_physicalPairedBranches
    hq hhard hcross
      (canonicalPhysicalPairedBranches_of_unitCyclePairedRepairs hrepairs)

end
end StatMech.FrontierD
