/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectEndpoint
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part2
open MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierB

noncomputable section

def ons_fixedPairRectDualPath (N : Nat) (a b : Site 2)
    (ha : a ∈ box 2 N) (hb : b ∈ box 2 N) (hab : a ≠ b) (n : Nat) :
    ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)) := by
  by_cases hN : N ≤ n + 1
  · exact ons_rectDualPathOfBoxVertices (n + 1)
      ⟨a, box_mono 2 hN ha⟩ ⟨b, box_mono 2 hN hb⟩
      (fun h => hab (congrArg Subtype.val h))
  · exact ons_originNeighborRectDualPath n

end
end StatMech.Onsager
