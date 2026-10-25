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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part15


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareNextDirection (n : Nat)
    (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) : FKIsingSquareDirection := by
  classical
  exact match d with
  | .east =>
      if fkIsingSquareDirectionAvailable n u .north then .north
      else if fkIsingSquareDirectionAvailable n u .west then .west
      else .south
  | .north =>
      if fkIsingSquareDirectionAvailable n u .west then .west
      else if fkIsingSquareDirectionAvailable n u .south then .south
      else .east
  | .west =>
      if fkIsingSquareDirectionAvailable n u .south then .south
      else if fkIsingSquareDirectionAvailable n u .east then .east
      else .north
  | .south =>
      if fkIsingSquareDirectionAvailable n u .east then .east
      else if fkIsingSquareDirectionAvailable n u .north then .north
      else .west


noncomputable def fkIsingSquarePreviousDirection (n : Nat)
    (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) : FKIsingSquareDirection := by
  classical
  exact match d with
  | .east =>
      if fkIsingSquareDirectionAvailable n u .south then .south
      else if fkIsingSquareDirectionAvailable n u .west then .west
      else .north
  | .north =>
      if fkIsingSquareDirectionAvailable n u .east then .east
      else if fkIsingSquareDirectionAvailable n u .south then .south
      else .west
  | .west =>
      if fkIsingSquareDirectionAvailable n u .north then .north
      else if fkIsingSquareDirectionAvailable n u .east then .east
      else .south
  | .south =>
      if fkIsingSquareDirectionAvailable n u .west then .west
      else if fkIsingSquareDirectionAvailable n u .north then .north
      else .east

end
end StatMech.Universality
