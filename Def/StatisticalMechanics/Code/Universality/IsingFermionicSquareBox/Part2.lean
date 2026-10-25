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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBoundaryVertex (n : Nat)
    (i : FKIsingSquareBoundaryIndex n) :
    (fkSquareBoxPlanar n).V :=
  ⟨fkIsingSquareBoundarySite n i, fkIsingSquareBoundarySite_mem_box n i⟩


def fkIsingSquareBoundaryOrderKey (n : Nat) :
    FKIsingSquareBoundaryIndex n -> Nat
  | (.bottom, k) => k.val
  | (.right, k) => 2 * n + k.val
  | (.top, k) => 4 * n + k.val
  | (.left, k) => 6 * n + k.val

end
end StatMech.Universality
