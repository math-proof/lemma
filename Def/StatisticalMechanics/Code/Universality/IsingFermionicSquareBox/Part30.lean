module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part32


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

noncomputable def fkIsingSquareExplorationPath (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).Path .source .terminal :=
  (fkIsingSquareLoopGraph_source_reachable_terminal n hn omega).some.toPath

def fkIsingSquareExplorationOrder (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    List (FKIsingSquareMedialCarrier n) :=
  (fkIsingSquareExplorationPath n hn omega :
    (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).support

end
end StatMech.Universality
