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
import Instance.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part2
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem localCIndicator_eq_ite_isCType
    (p : SixVertexLocalIncomingPattern) :
    localCIndicator p = if p.IsCType then 1 else 0 := by
  unfold localCIndicator SixVertexLocalIncomingPattern.IsCType
  decide +revert

theorem localCIndicator_localIncomingPattern
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    localCIndicator (sixVertexLocalIncomingPattern omega v) =
      if omega.IsCType v then 1 else 0 := by
  classical
  rw [localCIndicator_eq_ite_isCType]
  exact if_congr (sixVertexLocalIncomingPattern_isCType_iff omega v) rfl rfl


theorem sixVertexPairTotalC_mono_of_local
    {T : EvenTorus}
    (omega eta omega' eta' : SixVertexArrows T)
    (hlocal : forall v,
      localCIndicator (sixVertexLocalIncomingPattern omega v) +
          localCIndicator (sixVertexLocalIncomingPattern eta v) <=
        localCIndicator (sixVertexLocalIncomingPattern omega' v) +
          localCIndicator (sixVertexLocalIncomingPattern eta' v)) :
    sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <=
      sixVertexTorusCTypeCount omega' + sixVertexTorusCTypeCount eta' := by
  classical
  simp only [sixVertexTorusCTypeCount, <- Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  simpa only [localCIndicator_localIncomingPattern] using hlocal v


end ScratchLocalRetieC
