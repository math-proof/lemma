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
import Inductive.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part6


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareSourceAttachment (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n :=
  .dart (fkIsingSquareSourcePrimalEdge n hn, .west)


def fkIsingSquareTerminalAttachment (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n :=
  .dart (fkIsingSquareTerminalPrimalEdge n hn, .north)

end
end StatMech.Universality
