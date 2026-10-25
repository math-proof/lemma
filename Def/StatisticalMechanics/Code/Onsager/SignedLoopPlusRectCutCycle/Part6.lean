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
import Abbrev.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

def ons_rectHorizontalEdge {M N : Nat}
    (index : ons_RectHorizontalIndex M N) :
    Sym2 (ons_RectDualVertex M N) :=
  s((⟨index.1.val, by omega⟩, index.2),
    (⟨index.1.val + 1, by omega⟩, index.2))

def ons_rectVerticalEdge {M N : Nat}
    (index : ons_RectVerticalIndex M N) :
    Sym2 (ons_RectDualVertex M N) :=
  s((index.1, ⟨index.2.val, by omega⟩),
    (index.1, ⟨index.2.val + 1, by omega⟩))

end
end StatMech.Onsager
