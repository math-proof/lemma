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
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part11
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

def ons_plusRectPathEdgeSign (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v)
    (edge : Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1))) : Real :=
  if hedge : edge ∈
      (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset then
    (-1 : Real) ^ path.edges.countP (fun primal =>
      decide (primal =
        ((ons_touchingBondEquivRectDualEdge n).symm ⟨edge, hedge⟩).1))
  else 1


def ons_plusRectPathDefectSign (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v)
    (F : ons_PlusRectEvenSubgraph n) : Real :=
  ∏ edge ∈ F.1, ons_plusRectPathEdgeSign n path edge

end
end StatMech.Onsager
