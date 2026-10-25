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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part14


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareNextDirection_available (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareDirectionAvailable n u
      (fkIsingSquareNextDirection n u d) := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquareNextDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable] <;> omega

theorem fkIsingSquarePreviousDirection_available (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareDirectionAvailable n u
      (fkIsingSquarePreviousDirection n u d) := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquarePreviousDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable] <;> omega

theorem fkIsingSquarePreviousDirection_next (n : Nat) (_hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquarePreviousDirection n u
      (fkIsingSquareNextDirection n u d) = d := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable]

theorem fkIsingSquareNextDirection_previous (n : Nat) (_hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareNextDirection n u
      (fkIsingSquarePreviousDirection n u d) = d := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquareNextDirection,
      fkIsingSquarePreviousDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable]


end
end StatMech.Universality
