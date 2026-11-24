module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part5


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

def fkIsingSquareMarkedA (n : Nat) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int), -(n : Int)], by
    intro i
    fin_cases i <;> simp⟩


def fkIsingSquareMarkedB (n : Nat) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int), (n : Int)], by
    intro i
    fin_cases i <;> simp⟩


def fkIsingSquareMarkedAIndex (n : Nat) (hn : 0 < n) :
    FKIsingSquareBoundaryIndex n :=
  (.bottom, ⟨0, by omega⟩)


def fkIsingSquareMarkedBIndex (n : Nat) (hn : 0 < n) :
    FKIsingSquareBoundaryIndex n :=
  (.left, ⟨0, by omega⟩)

end
end StatMech.Universality
