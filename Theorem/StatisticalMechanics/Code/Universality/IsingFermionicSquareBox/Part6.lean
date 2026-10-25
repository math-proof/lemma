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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part5


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryVertex_markedA (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryVertex n (fkIsingSquareMarkedAIndex n hn) =
      fkIsingSquareMarkedA n := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [fkIsingSquareBoundaryVertex, fkIsingSquareMarkedAIndex,
      fkIsingSquareBoundarySite, fkIsingSquareMarkedA]

theorem fkIsingSquareBoundaryVertex_markedB (n : Nat) (hn : 0 < n) :
    fkIsingSquareBoundaryVertex n (fkIsingSquareMarkedBIndex n hn) =
      fkIsingSquareMarkedB n := by
  apply Subtype.ext
  funext i
  fin_cases i <;>
    simp [fkIsingSquareBoundaryVertex, fkIsingSquareMarkedBIndex,
      fkIsingSquareBoundarySite, fkIsingSquareMarkedB]


end
end StatMech.Universality
