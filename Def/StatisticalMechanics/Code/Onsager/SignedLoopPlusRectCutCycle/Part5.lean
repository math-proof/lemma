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
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part4
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

def ons_boxToPlusWiredSupportHom (n : Nat) :
    StatMech.FK.boxGraph 2 n →g
      ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n) where
  toFun := some
  map_rel' := by
    intro x y hxy
    exact ons_multibondSupportGraph_plusWired_adj_some n x y hxy

def ons_plusWiredEastSite (n : Nat) : Site 2 := ![(n : Int), 0]

def ons_plusWiredEastOutsideSite (n : Nat) : Site 2 := ![(n : Int) + 1, 0]

end
end StatMech.Onsager
