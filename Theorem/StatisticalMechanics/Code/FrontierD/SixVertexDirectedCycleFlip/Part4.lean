/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part4


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexDirectedCycleFlipMask.balanced
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (hmask : SixVertexDirectedCycleFlipMask omega mask) :
    SixVertexBalancedFlipMask omega mask := by
  intro v
  exact sixVertexLocalBalancedFlipMask_of_cycle _ _ (hmask v)


theorem sixVertexTorusFlip_ice_of_balanced
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (homega : omega.IceRule)
    (hmask : SixVertexBalancedFlipMask omega mask) :
    (sixVertexTorusFlip mask omega).IceRule := by
  intro v
  have hlocal := sixVertexLocalFlipMask_ice_of_balanced
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexTorusLocalSwitchMask mask v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (hmask v)
  rw [SixVertexLocalIncomingPattern.Ice] at hlocal
  rw [← sixVertexLocalIncomingPattern_count,
    sixVertexLocalIncomingPattern_torusFlip]
  exact hlocal


theorem sixVertexBalancedFlipMask_of_ice_flip
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (homega : omega.IceRule)
    (hflip : (sixVertexTorusFlip mask omega).IceRule) :
    SixVertexBalancedFlipMask omega mask := by
  intro v
  apply sixVertexLocalBalancedFlipMask_of_ice_flip
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexTorusLocalSwitchMask mask v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
  rw [← sixVertexLocalIncomingPattern_torusFlip]
  exact sixVertexLocalIncomingPattern_ice _ hflip v


theorem SixVertexBalancedFlipMask.maskXor
    {T : EvenTorus} {omega first second : SixVertexArrows T}
    (homega : omega.IceRule)
    (hfirst : SixVertexBalancedFlipMask omega first)
    (hsecond : SixVertexBalancedFlipMask
      (sixVertexTorusFlip first omega) second) :
    SixVertexBalancedFlipMask omega
      (sixVertexTorusMaskXor first second) := by
  apply sixVertexBalancedFlipMask_of_ice_flip homega
  rw [← sixVertexTorusFlip_maskXor]
  exact sixVertexTorusFlip_ice_of_balanced
    (sixVertexTorusFlip_ice_of_balanced homega hfirst) hsecond


theorem sixVertexTorusFlip_maskXor_eq
    {T : EvenTorus} (first second omega : SixVertexArrows T) :
    sixVertexTorusFlip (sixVertexTorusMaskXor first second) omega =
      sixVertexTorusFlip second (sixVertexTorusFlip first omega) :=
  (sixVertexTorusFlip_maskXor first second omega).symm


theorem SixVertexBalancedFlipMask.after_flip
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (hmask : SixVertexBalancedFlipMask omega mask) :
    SixVertexBalancedFlipMask (sixVertexTorusFlip mask omega) mask := by
  intro v
  rw [sixVertexLocalIncomingPattern_torusFlip]
  exact (hmask v).after_flip _ _


theorem sixVertexTorusFlip_ice
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (homega : omega.IceRule)
    (hmask : SixVertexDirectedCycleFlipMask omega mask) :
    (sixVertexTorusFlip mask omega).IceRule := by
  intro v
  have hlocal := sixVertexLocalFlipMask_ice
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexTorusLocalSwitchMask mask v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (hmask v)
  rw [SixVertexLocalIncomingPattern.Ice] at hlocal
  rw [← sixVertexLocalIncomingPattern_count]
  rw [sixVertexLocalIncomingPattern_torusFlip]
  exact hlocal


theorem SixVertexDirectedCycleFlipMask.after_flip
    {T : EvenTorus} {omega mask : SixVertexArrows T}
    (hmask : SixVertexDirectedCycleFlipMask omega mask) :
    SixVertexDirectedCycleFlipMask (sixVertexTorusFlip mask omega) mask := by
  intro v
  rcases hmask v with hzero | ⟨htwo, hone⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨htwo, ?_⟩
    rw [sixVertexLocalIncomingPattern_torusFlip]
    exact sixVertexLocalSelectedIncomingCount_flip _ _ htwo hone


end
end StatMech.FrontierD
