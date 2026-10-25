/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCappedTent
import Def.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part3


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem fullVertexColumnIndex_coe
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    (fullVertexColumnIndex n x : Int) = x.1 0 + (n : Int) := by
  unfold fullVertexColumnIndex
  rw [Int.toNat_of_nonneg]
  have hx := (fkIsingSquareVertex_coordinate_bounds n x 0).1
  omega

theorem fullVertexRowIndex_coe
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    (fullVertexRowIndex n x : Int) = x.1 1 + (n : Int) := by
  unfold fullVertexRowIndex
  rw [Int.toNat_of_nonneg]
  have hx := (fkIsingSquareVertex_coordinate_bounds n x 1).1
  omega

theorem fullVertexColumnIndex_le
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    fullVertexColumnIndex n x <= 2 * n := by
  have hx := (fkIsingSquareVertex_coordinate_bounds n x 0).2
  have hcoe := fullVertexColumnIndex_coe n x
  exact_mod_cast (show (fullVertexColumnIndex n x : Int) <=
      2 * (n : Int) by omega)

theorem fullVertexRowIndex_le
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    fullVertexRowIndex n x <= 2 * n := by
  have hx := (fkIsingSquareVertex_coordinate_bounds n x 1).2
  have hcoe := fullVertexRowIndex_coe n x
  exact_mod_cast (show (fullVertexRowIndex n x : Int) <=
      2 * (n : Int) by omega)

@[simp] theorem fullVertexColumnIndex_neighbor_east
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .east) :
    fullVertexColumnIndex n (fkIsingSquareNeighbor n x .east h) =
      fullVertexColumnIndex n x + 1 := by
  have hnext := fullVertexColumnIndex_coe n
    (fkIsingSquareNeighbor n x .east h)
  have hbase := fullVertexColumnIndex_coe n x
  apply Int.ofNat_inj.mp
  push_cast
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 0 + 1 + (n : Int) = x.1 0 + (n : Int) + 1
  ring

@[simp] theorem fullVertexColumnIndex_neighbor_west
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .west) :
    fullVertexColumnIndex n (fkIsingSquareNeighbor n x .west h) =
      fullVertexColumnIndex n x - 1 := by
  have hpos : 0 < fullVertexColumnIndex n x := by
    have hcoe := fullVertexColumnIndex_coe n x
    simp [fkIsingSquareDirectionAvailable] at h
    omega
  have hnext := fullVertexColumnIndex_coe n
    (fkIsingSquareNeighbor n x .west h)
  have hbase := fullVertexColumnIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))]
  push_cast
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 0 - 1 + (n : Int) = x.1 0 + (n : Int) - 1
  ring

@[simp] theorem fullVertexColumnIndex_neighbor_north
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .north) :
    fullVertexColumnIndex n (fkIsingSquareNeighbor n x .north h) =
      fullVertexColumnIndex n x := by
  have hnext := fullVertexColumnIndex_coe n
    (fkIsingSquareNeighbor n x .north h)
  have hbase := fullVertexColumnIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 0 = x.1 0
  rfl

@[simp] theorem fullVertexColumnIndex_neighbor_south
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .south) :
    fullVertexColumnIndex n (fkIsingSquareNeighbor n x .south h) =
      fullVertexColumnIndex n x := by
  have hnext := fullVertexColumnIndex_coe n
    (fkIsingSquareNeighbor n x .south h)
  have hbase := fullVertexColumnIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 0 = x.1 0
  rfl

@[simp] theorem fullVertexRowIndex_neighbor_north
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .north) :
    fullVertexRowIndex n (fkIsingSquareNeighbor n x .north h) =
      fullVertexRowIndex n x + 1 := by
  have hnext := fullVertexRowIndex_coe n
    (fkIsingSquareNeighbor n x .north h)
  have hbase := fullVertexRowIndex_coe n x
  apply Int.ofNat_inj.mp
  push_cast
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 1 + 1 + (n : Int) = x.1 1 + (n : Int) + 1
  ring

@[simp] theorem fullVertexRowIndex_neighbor_south
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .south) :
    fullVertexRowIndex n (fkIsingSquareNeighbor n x .south h) =
      fullVertexRowIndex n x - 1 := by
  have hpos : 0 < fullVertexRowIndex n x := by
    have hcoe := fullVertexRowIndex_coe n x
    simp [fkIsingSquareDirectionAvailable] at h
    omega
  have hnext := fullVertexRowIndex_coe n
    (fkIsingSquareNeighbor n x .south h)
  have hbase := fullVertexRowIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))]
  push_cast
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 1 - 1 + (n : Int) = x.1 1 + (n : Int) - 1
  ring

@[simp] theorem fullVertexRowIndex_neighbor_east
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .east) :
    fullVertexRowIndex n (fkIsingSquareNeighbor n x .east h) =
      fullVertexRowIndex n x := by
  have hnext := fullVertexRowIndex_coe n
    (fkIsingSquareNeighbor n x .east h)
  have hbase := fullVertexRowIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 1 = x.1 1
  rfl

@[simp] theorem fullVertexRowIndex_neighbor_west
    (n : Nat) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .west) :
    fullVertexRowIndex n (fkIsingSquareNeighbor n x .west h) =
      fullVertexRowIndex n x := by
  have hnext := fullVertexRowIndex_coe n
    (fkIsingSquareNeighbor n x .west h)
  have hbase := fullVertexRowIndex_coe n x
  apply Int.ofNat_inj.mp
  rw [hnext, hbase]
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  change x.1 1 = x.1 1
  rfl


theorem fullVertexColumnFunction_laplacian
    (n : Nat) (F : Nat -> Real) (x : FKIsingSquareFullVertexNode n)
    (hleft : -(n : Int) < x.1 0) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => F (fullVertexColumnIndex n y)) x =
      if x.1 0 = (n : Int) then
        F (fullVertexColumnIndex n x - 1) - F (fullVertexColumnIndex n x)
      else
        F (fullVertexColumnIndex n x + 1) +
          F (fullVertexColumnIndex n x - 1) -
            2 * F (fullVertexColumnIndex n x) := by
  rw [fullVertex_laplacian_eq_directionIncrements]
  have hwest : fkIsingSquareDirectionAvailable n x .west := hleft
  have hcol : 0 < fullVertexColumnIndex n x := by
    have hcoe := fullVertexColumnIndex_coe n x
    omega
  have hnorth : fullVertexDirectionIncrement n
      (fun y => F (fullVertexColumnIndex n y)) x .north = 0 := by
    unfold fullVertexDirectionIncrement
    split_ifs with h
    · simp
    · rfl
  have hsouth : fullVertexDirectionIncrement n
      (fun y => F (fullVertexColumnIndex n y)) x .south = 0 := by
    unfold fullVertexDirectionIncrement
    split_ifs with h
    · simp
    · rfl
  rw [hnorth, hsouth]
  by_cases hright : x.1 0 = (n : Int)
  · have heast : Not (fkIsingSquareDirectionAvailable n x .east) := by
      simp [fkIsingSquareDirectionAvailable, hright]
    simp [fullVertexDirectionIncrement, hright, heast, hwest]
  · have heast : fkIsingSquareDirectionAvailable n x .east := by
      have hx := (fkIsingSquareVertex_coordinate_bounds n x 0).2
      simp [fkIsingSquareDirectionAvailable]
      omega
    simp [fullVertexDirectionIncrement, hright, heast, hwest]
    ring


theorem fullVertexRowFunction_laplacian
    (n : Nat) (F : Nat -> Real) (x : FKIsingSquareFullVertexNode n)
    (hn : 0 < n) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => F (fullVertexRowIndex n y)) x =
      if x.1 1 = -(n : Int) then
        F (fullVertexRowIndex n x + 1) - F (fullVertexRowIndex n x)
      else if x.1 1 = (n : Int) then
        F (fullVertexRowIndex n x - 1) - F (fullVertexRowIndex n x)
      else
        F (fullVertexRowIndex n x + 1) +
          F (fullVertexRowIndex n x - 1) -
            2 * F (fullVertexRowIndex n x) := by
  rw [fullVertex_laplacian_eq_directionIncrements]
  have heast : fullVertexDirectionIncrement n
      (fun y => F (fullVertexRowIndex n y)) x .east = 0 := by
    unfold fullVertexDirectionIncrement
    split_ifs with h
    · simp
    · rfl
  have hwest : fullVertexDirectionIncrement n
      (fun y => F (fullVertexRowIndex n y)) x .west = 0 := by
    unfold fullVertexDirectionIncrement
    split_ifs with h
    · simp
    · rfl
  rw [heast, hwest]
  by_cases hbottom : x.1 1 = -(n : Int)
  · have hsouth : Not (fkIsingSquareDirectionAvailable n x .south) := by
      simp [fkIsingSquareDirectionAvailable, hbottom]
    have hnorth : fkIsingSquareDirectionAvailable n x .north := by
      simp [fkIsingSquareDirectionAvailable, hbottom]
      omega
    simp [fullVertexDirectionIncrement, hbottom, hsouth, hnorth]
  · by_cases htop : x.1 1 = (n : Int)
    · have hnorth : Not (fkIsingSquareDirectionAvailable n x .north) := by
        simp [fkIsingSquareDirectionAvailable, htop]
      have hsouth : fkIsingSquareDirectionAvailable n x .south := by
        simp [fkIsingSquareDirectionAvailable, htop]
        omega
      simp [fullVertexDirectionIncrement, htop, hsouth, hnorth,
        hn.ne']
    · have hnorth : fkIsingSquareDirectionAvailable n x .north := by
        have hx := fkIsingSquareVertex_coordinate_bounds n x 1
        simp [fkIsingSquareDirectionAvailable]
        omega
      have hsouth : fkIsingSquareDirectionAvailable n x .south := by
        have hx := fkIsingSquareVertex_coordinate_bounds n x 1
        simp [fkIsingSquareDirectionAvailable]
        omega
      simp [fullVertexDirectionIncrement, hbottom, htop, hsouth, hnorth]
      ring


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
