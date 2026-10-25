/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part18


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_eq_selectedDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    seed.selected x = seed.selectedDart x.1 := by
  rcases x with ⟨d, branch⟩
  cases branch
  · rfl
  · exact seed.selected_branchSwap (d, false)


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (d : SixVertexOrientedDisagreementDart omega eta) :
    seed.synchronizedAt d ↔
      seed.selectedDart
          (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d) =
        seed.selectedDart
          (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt
    SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionBit
    sixVertexDegreeTwoBranchPredecessor
  simp only [SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_eq_selectedDart]
  have hcurrent : seed.selectedDart d =
      seed.selectedDart d := rfl
  generalize hcur : seed.selectedDart d = current
  generalize hfalse : seed.selectedDart
      ((doubledAlignedFirstReturnPerm homega heta hdegree).symm
        (d, false)).1 = predecessorFalse
  generalize htrue : seed.selectedDart
      ((doubledAlignedFirstReturnPerm homega heta hdegree).symm
        (d, true)).1 = predecessorTrue
  cases current <;> cases predecessorFalse <;> cases predecessorTrue <;>
    simp_all


end
end StatMech.FrontierD
