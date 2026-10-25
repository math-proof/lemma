/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Structure.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part2
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem DoubledAlignedUnitOrbitSplit.first_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (split : DoubledAlignedUnitOrbitSplit homega heta hdegree) :
    split.first.Nodup := by
  have hall := alignedPermOrderedAllOrbits_nodup
    (doubledAlignedFirstReturnPerm homega heta hdegree)
  rw [split.split] at hall
  exact hall.of_append_left

theorem exists_doubledAlignedUnitOrbitSplit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    Nonempty (DoubledAlignedUnitOrbitSplit homega heta hdegree) := by
  obtain ⟨first, second, hsplit, hfirst, hsecond⟩ :=
    exists_two_unit_blocks_of_alignedPermOrderedAllOrbits
      (doubledAlignedFirstReturnPerm homega heta hdegree)
      (doubledAlignedCharge hdegree)
      (doubledAlignedCharge_zeroOrUnit hdegree)
      (by
        rw [Fintype.sum_prod_type]
        exact sum_doubledAlignedCharge_eq_two homega heta hdegree n
          homegaSector hetaSector hn)
  exact ⟨⟨first, second, hsplit, hfirst, hsecond⟩⟩

end ScratchLocalRetieC
