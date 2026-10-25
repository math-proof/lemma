/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_nonempty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    Nonempty (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) := by
  cases hstates : seed.splitStates with
  | nil => exact False.elim (seed.splitStates_ne_nil hstates)
  | cons x states =>
      refine ⟨⟨doubledAlignedBlackDart homega heta hdegree false x, ?_⟩⟩
      rw [doubledAlignedBlackDart_mem_boundarySegments_iff, hstates]
      simp


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_card_pos
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    0 < Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) :=
  Fintype.card_pos_iff.mpr seed.splitBoundary_nonempty


end
end StatMech.FrontierD
