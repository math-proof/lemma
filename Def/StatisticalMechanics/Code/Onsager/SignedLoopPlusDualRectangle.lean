/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

def ons_plusDualFaceBox (n : Nat) : Set (Site 2) :=
  {f | forall i, -(n : Int) - 1 <= f i ∧ f i <= n}


def ons_plusDualFaceEdgeSet (n : Nat) : Set (Sym2 (Site 2)) :=
  {edge | edge ∈ (hypercubicLattice 2).edgeSet ∧
    forall f, f ∈ edge -> f ∈ ons_plusDualFaceBox n}


end
end StatMech.Onsager
