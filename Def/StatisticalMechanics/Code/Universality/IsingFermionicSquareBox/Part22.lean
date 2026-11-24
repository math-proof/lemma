module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Inductive.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
