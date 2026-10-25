/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

@[simp] theorem fkIsingSquareRadialPatchEdge_orientation
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm i j) =
      fkIsingSquareDirectionEdgeOrientation n
        (fkIsingSquareRadialPatchVertex n m hm i j)
        (fkIsingSquareRadialPatchDirection i.1 j.1)
        (fkIsingSquareRadialPatchDirection_available n m hm i j) :=
  fkIsingSquareOrientedEdge_directionEdge n _ _ _

theorem fkIsingSquareRadialPatchEdge_eq_east
    (n m : Nat) (hm : m ≤ n) (i j : Fin m)
    (heven : Even (i.1 + j.1)) :
    fkIsingSquareRadialPatchEdge n m hm i j =
      fkIsingSquareDirectionEdge n
        (fkIsingSquareRadialPatchVertex n m hm i j) .east
        (by simpa [fkIsingSquareRadialPatchDirection, heven] using
          fkIsingSquareRadialPatchDirection_available n m hm i j) := by
  unfold fkIsingSquareRadialPatchEdge
  simp only [fkIsingSquareRadialPatchDirection, if_pos heven]

theorem fkIsingSquareRadialPatchEdge_eq_north
    (n m : Nat) (hm : m ≤ n) (i j : Fin m)
    (hodd : ¬ Even (i.1 + j.1)) :
    fkIsingSquareRadialPatchEdge n m hm i j =
      fkIsingSquareDirectionEdge n
        (fkIsingSquareRadialPatchVertex n m hm i j) .north
        (by simpa [fkIsingSquareRadialPatchDirection, hodd] using
          fkIsingSquareRadialPatchDirection_available n m hm i j) := by
  unfold fkIsingSquareRadialPatchEdge
  simp only [fkIsingSquareRadialPatchDirection, if_neg hodd]

@[simp] theorem fkIsingSquareDartEndpoint_directionEdge_east
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .east)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartEndpoint n
        (fkIsingSquareDirectionEdge n u .east hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => u
      | .head => fkIsingSquareNeighbor n u .east hu := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartDirection_directionEdge_east
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .east)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartDirection n
        (fkIsingSquareDirectionEdge n u .east hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .east
      | .head => .west := by
  unfold fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartEndpoint_directionEdge_north
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .north)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartEndpoint n
        (fkIsingSquareDirectionEdge n u .north hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => u
      | .head => fkIsingSquareNeighbor n u .north hu := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartDirection_directionEdge_north
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .north)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartDirection n
        (fkIsingSquareDirectionEdge n u .north hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .north
      | .head => .south := by
  unfold fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartEndpoint_directionEdge_south
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .south)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartEndpoint n
        (fkIsingSquareDirectionEdge n u .south hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => fkIsingSquareNeighbor n u .south hu
      | .head => u := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

@[simp] theorem fkIsingSquareDartDirection_directionEdge_south
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (hu : fkIsingSquareDirectionAvailable n u .south)
    (s : FKIsingMedialSide) :
    fkIsingSquareDartDirection n
        (fkIsingSquareDirectionEdge n u .south hu, s) =
      match (fkIsingSquareSideCorner s).1 with
      | .tail => .north
      | .head => .south := by
  unfold fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;> rfl

theorem fkIsingSquareRadialPatchWedgeFaceKey_of_even
    (n m : Nat) (hm : m ≤ n) (i j : Fin m)
    (heven : Even (i.1 + j.1)) (s : FKIsingMedialSide) :
    fkIsingSquareWedgeFaceKey n
        (fkIsingSquareRadialPatchEdge n m hm i j, s) =
      match s with
      | .west | .north =>
          ((fkIsingSquareRadialPatchHalf i.1 j.1 : Int),
            (i.1 : Int) - fkIsingSquareRadialPatchHalf i.1 j.1)
      | .east | .south =>
          ((fkIsingSquareRadialPatchHalf i.1 j.1 : Int),
            (i.1 : Int) - fkIsingSquareRadialPatchHalf i.1 j.1 - 1) := by
  rw [fkIsingSquareRadialPatchEdge_eq_east n m hm i j heven]
  unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
    fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;>
    simp [fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareRadialPatchVertex, fkIsingSquareSideCorner]

theorem fkIsingSquareRadialPatchWedgeFaceKey_of_odd
    (n m : Nat) (hm : m ≤ n) (i j : Fin m)
    (hodd : ¬ Even (i.1 + j.1)) (s : FKIsingMedialSide) :
    fkIsingSquareWedgeFaceKey n
        (fkIsingSquareRadialPatchEdge n m hm i j, s) =
      match s with
      | .west | .north =>
          ((fkIsingSquareRadialPatchHalf i.1 j.1 : Int) - 1,
            (i.1 : Int) - fkIsingSquareRadialPatchHalf i.1 j.1)
      | .east | .south =>
          ((fkIsingSquareRadialPatchHalf i.1 j.1 : Int),
            (i.1 : Int) - fkIsingSquareRadialPatchHalf i.1 j.1) := by
  rw [fkIsingSquareRadialPatchEdge_eq_north n m hm i j hodd]
  unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
    fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases s <;>
    simp [fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareRadialPatchVertex, fkIsingSquareSideCorner]


end
end StatMech.Universality
