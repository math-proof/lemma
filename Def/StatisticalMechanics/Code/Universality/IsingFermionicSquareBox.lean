/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBoundarySite (n : Nat) :
    FKIsingSquareBoundaryIndex n -> Site 2
  | (.bottom, k) => ![(k.val : Int) - n, -(n : Int)]
  | (.right, k) => ![(n : Int), (k.val : Int) - n]
  | (.top, k) => ![(n : Int) - k.val, (n : Int)]
  | (.left, k) => ![-(n : Int), (n : Int) - k.val]

end
end StatMech.Universality
