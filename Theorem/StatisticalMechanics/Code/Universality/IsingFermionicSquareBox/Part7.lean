module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part6


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

theorem fkIsingSquareMarkedA_mem_wiredArc (n : Nat) :
    fkIsingSquareWiredArc n (fkIsingSquareMarkedA n) := by
  rfl

theorem fkIsingSquareMarkedB_mem_wiredArc (n : Nat) :
    fkIsingSquareWiredArc n (fkIsingSquareMarkedB n) := by
  rfl

theorem fkIsingSquareBoundary_left_mem_wiredArc (n : Nat)
    (k : Fin (2 * n)) :
    fkIsingSquareWiredArc n
      (fkIsingSquareBoundaryVertex n (.left, k)) := by
  rfl


end
end StatMech.Universality
