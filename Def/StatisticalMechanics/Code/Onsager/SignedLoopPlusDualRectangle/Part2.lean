module
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
public import Abbrev.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

def ons_plusDualFaceGraph (n : Nat) : SimpleGraph (ons_PlusDualFaceVertex n) :=
  (hypercubicLattice 2).induce (ons_plusDualFaceBox n)

end
end StatMech.Onsager
