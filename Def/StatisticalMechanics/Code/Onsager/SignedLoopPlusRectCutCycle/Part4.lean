module
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
public import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
public import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part3
open Finset SimpleGraph
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

def ons_plusRectContour (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    Finset (Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1))) :=
  transportEdges (ons_plusDualFaceEquivRect n) (ons_plusDualContourFace n tau)

end
end StatMech.Onsager
