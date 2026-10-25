/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part2
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

def ons_plusDualContourFace (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    Finset (Sym2 (ons_PlusDualFaceVertex n)) :=
  (ons_plusDualContour n tau).attach.map
    ⟨fun edge => ons_plusDualFaceEdgeLift n
        ⟨edge.1, ons_plusDualContour_subset_plusDualFaceEdgeSet n tau edge.1 edge.2⟩,
      by
        intro edge edge' h
        apply Subtype.ext
        have hmap := congrArg (Sym2.map Subtype.val) h
        simpa using hmap⟩

end
end StatMech.Onsager
