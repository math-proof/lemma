/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareHoleFill
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

def squareOuterComponent (S : Set (Site 2)) (hS : S.Finite) : Set (Site 2) :=
  {x | (latticeMinusBarrier S).Reachable
    (beacon 2 (squareHoleFillRadius S hS)) x}


def squareHoleFill (S : Set (Site 2)) (hS : S.Finite) : Set (Site 2) :=
  (squareOuterComponent S hS)ᶜ

end
end StatMech.FrontierD
