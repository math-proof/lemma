/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part3


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem sixVertexDegreeTwoSynchronizedComponentCharge_le_positiveDarts
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component ≤
      (sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree
        component).card := by
  classical
  unfold sixVertexDegreeTwoSynchronizedComponentCharge
  calc
    (∑ dart : SixVertexOrientedDisagreementDart omega eta,
      if (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          dart = component then
        sixVertexDegreeTwoStrandStepSeamSign hdegree dart else 0) ≤
        ∑ dart : SixVertexOrientedDisagreementDart omega eta,
          if dart ∈ sixVertexDegreeTwoSynchronizedComponentPositiveDarts
              homega heta hdegree component then (1 : Int) else 0 := by
      apply Finset.sum_le_sum
      intro dart _
      by_cases hcomponent :
          (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
            dart = component
      · rcases sixVertexDegreeTwoOrderedStep_zeroOrUnit hdegree dart with
          hzero | hpos | hneg
        · simp [sixVertexDegreeTwoSynchronizedComponentPositiveDarts,
            hcomponent, hzero]
        · simp [sixVertexDegreeTwoSynchronizedComponentPositiveDarts,
            hcomponent, hpos]
        · simp [sixVertexDegreeTwoSynchronizedComponentPositiveDarts,
            hcomponent, hneg]
      · simp [sixVertexDegreeTwoSynchronizedComponentPositiveDarts, hcomponent]
    _ = (sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree
          component).card := by
      simp


theorem exists_two_sixVertexDegreeTwoSynchronizedComponentPositiveDarts
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hcharge : 2 ≤
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component) :
    ∃ first second : SixVertexOrientedDisagreementDart omega eta,
      first ≠ second /\
        first ∈ sixVertexDegreeTwoSynchronizedComponentPositiveDarts
          homega heta hdegree component /\
        second ∈ sixVertexDegreeTwoSynchronizedComponentPositiveDarts
          homega heta hdegree component := by
  classical
  let positive := sixVertexDegreeTwoSynchronizedComponentPositiveDarts
    homega heta hdegree component
  have hcardInt : (2 : Int) ≤ positive.card :=
    hcharge.trans
      (sixVertexDegreeTwoSynchronizedComponentCharge_le_positiveDarts
        homega heta hdegree component)
  have hcard : 1 < Fintype.card {dart // dart ∈ positive} := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨first, second, hne⟩ := Fintype.exists_pair_of_one_lt_card hcard
  exact ⟨first, second, fun heq => hne (Subtype.ext heq), first.2, second.2⟩


end
end StatMech.FrontierD
