/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Def.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fullVertex_laplacian_eq_directionIncrements
    (n : Nat) (F : FKIsingSquareFullVertexNode n -> Real)
    (x : FKIsingSquareFullVertexNode n) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) F x =
      fullVertexDirectionIncrement n F x .east +
        fullVertexDirectionIncrement n F x .north +
        fullVertexDirectionIncrement n F x .west +
        fullVertexDirectionIncrement n F x .south := by
  classical
  rw [fullVertex_laplacian_eq_sum_available]
  calc
    (∑ d : FKIsingSquareAvailableDirection n x,
        (F (fkIsingSquareAvailableNeighbor n x d) - F x)) =
        ∑ d : FKIsingSquareAvailableDirection n x,
          fullVertexDirectionIncrement n F x d.1 := by
      apply Finset.sum_congr rfl
      intro d _
      simp [fullVertexDirectionIncrement, d.2,
        fkIsingSquareAvailableNeighbor]
    _ = ∑ d ∈ Finset.univ.filter
          (fkIsingSquareDirectionAvailable n x),
          fullVertexDirectionIncrement n F x d := by
      symm
      exact Finset.sum_subtype
        (Finset.univ.filter (fkIsingSquareDirectionAvailable n x))
        (by simp) (fullVertexDirectionIncrement n F x)
    _ = _ := by
      rw [show (Finset.univ : Finset FKIsingSquareDirection) =
          {.east, .north, .west, .south} by
        ext d
        fin_cases d <;> simp]
      rw [Finset.sum_filter]
      by_cases he : fkIsingSquareDirectionAvailable n x .east <;>
        by_cases hnorth : fkIsingSquareDirectionAvailable n x .north <;>
        by_cases hw : fkIsingSquareDirectionAvailable n x .west <;>
        by_cases hs : fkIsingSquareDirectionAvailable n x .south <;>
        simp [he, hnorth, hw, hs, fullVertexDirectionIncrement]
      all_goals ring


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
