module
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
public import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
public import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part6
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

def ons_rectHorizontalEdges (M N : Nat) :
    Finset (Sym2 (ons_RectDualVertex M N)) :=
  Finset.univ.map
    ⟨ons_rectHorizontalEdge, ons_rectHorizontalEdge_injective M N⟩

def ons_rectVerticalEdges (M N : Nat) :
    Finset (Sym2 (ons_RectDualVertex M N)) :=
  Finset.univ.map
    ⟨ons_rectVerticalEdge, ons_rectVerticalEdge_injective M N⟩

end
end StatMech.Onsager
