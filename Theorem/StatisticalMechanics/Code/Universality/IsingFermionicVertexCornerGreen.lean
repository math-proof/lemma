/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Def.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fkIsingSquareAvailableNeighbor_injective
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Function.Injective (fkIsingSquareAvailableNeighbor n x) := by
  intro d e h
  apply Subtype.ext
  exact fkIsingSquareNeighbor_injective n x d.1 e.1 d.2 e.2 h


theorem fkIsingSquareFullVertex_neighborFinset_eq_available
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    [Fintype ↑((fkIsingSquareFullVertexGraph n).neighborSet x)] :
    (fkIsingSquareFullVertexGraph n).neighborFinset x =
      Finset.univ.image (fkIsingSquareAvailableNeighbor n x) := by
  classical
  ext y
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  constructor
  · intro hxy
    change (hypercubicLattice 2).Adj x.1 y.1 at hxy
    rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
    · have hd : fkIsingSquareDirectionAvailable n x .west := by
        have hy := fkIsingSquareVertex_coordinate_bounds n y 0
        have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        simp [fkIsingSquareDirectionAvailable]
        omega
      refine ⟨⟨.west, hd⟩, Finset.mem_univ _, ?_⟩
      symm
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        change y.1 0 = x.1 0 - 1
        omega
      · have hk := congrFun h 1
        simpa [fkIsingSquareAvailableNeighbor, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, Pi.add_apply] using hk.symm
    · have hd : fkIsingSquareDirectionAvailable n x .east := by
        have hy := fkIsingSquareVertex_coordinate_bounds n y 0
        have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        simp [fkIsingSquareDirectionAvailable]
        omega
      refine ⟨⟨.east, hd⟩, Finset.mem_univ _, ?_⟩
      symm
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        change y.1 0 = x.1 0 + 1
        omega
      · have hk := congrFun h 1
        simpa [fkIsingSquareAvailableNeighbor, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, Pi.add_apply] using hk.symm
    · have hd : fkIsingSquareDirectionAvailable n x .south := by
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        simp [fkIsingSquareDirectionAvailable]
        omega
      refine ⟨⟨.south, hd⟩, Finset.mem_univ _, ?_⟩
      symm
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simpa [fkIsingSquareAvailableNeighbor, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, Pi.add_apply] using hk.symm
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        change y.1 1 = x.1 1 - 1
        omega
    · have hd : fkIsingSquareDirectionAvailable n x .north := by
        have hy := fkIsingSquareVertex_coordinate_bounds n y 1
        have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        simp [fkIsingSquareDirectionAvailable]
        omega
      refine ⟨⟨.north, hd⟩, Finset.mem_univ _, ?_⟩
      symm
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simpa [fkIsingSquareAvailableNeighbor, fkIsingSquareNeighbor,
          fkIsingSquareNeighborSite, Pi.add_apply] using hk.symm
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        change y.1 1 = x.1 1 + 1
        omega
  · rintro ⟨d, -, rfl⟩
    exact fkIsingSquare_adj_neighbor n x d.1 d.2


theorem fullVertex_laplacian_eq_sum_available
    (n : Nat) (F : FKIsingSquareFullVertexNode n -> Real)
    (x : FKIsingSquareFullVertexNode n) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) F x =
      ∑ d : FKIsingSquareAvailableDirection n x,
        (F (fkIsingSquareAvailableNeighbor n x d) - F x) := by
  classical
  unfold isingFiniteGraphLaplacian
  rw [fkIsingSquareFullVertex_neighborFinset_eq_available]
  rw [Finset.sum_image]
  exact fun d _ e _ h => fkIsingSquareAvailableNeighbor_injective n x h


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
