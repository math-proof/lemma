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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part20


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBondMate_involutive (n : Nat) (hn : 0 < n) :
    Function.Involutive (fkIsingSquareBondMate n hn) := by
  intro x
  cases ht : (fkIsingSquareSideCorner x.2).2
  · simp only [fkIsingSquareBondMate, ht,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir := fkIsingSquarePreviousDirection_next n hn _ _
      (fkIsingSquareDartDirection_available n x)
    calc
      _ = fkIsingSquareDirectionDart n
          (fkIsingSquareDartEndpoint n x)
          (fkIsingSquareDartDirection n x)
          (fkIsingSquareDartDirection_available n x)
          .counterclockwise :=
        fkIsingSquareDirectionDart_congr n _ hdir _ _ _
      _ = x := by
        simpa [ht] using fkIsingSquareDirectionDart_reconstruct n x

  · simp only [fkIsingSquareBondMate, ht,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn]
    have hdir := fkIsingSquareNextDirection_previous n hn _ _
      (fkIsingSquareDartDirection_available n x)
    calc
      _ = fkIsingSquareDirectionDart n
          (fkIsingSquareDartEndpoint n x)
          (fkIsingSquareDartDirection n x)
          (fkIsingSquareDartDirection_available n x) .clockwise :=
        fkIsingSquareDirectionDart_congr n _ hdir _ _ _
      _ = x := by
        simpa [ht] using fkIsingSquareDirectionDart_reconstruct n x

@[simp] theorem fkIsingSquareDartEndpoint_bondMate
    (n : Nat) (hn : 0 < n)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDartEndpoint n (fkIsingSquareBondMate n hn x) =
      fkIsingSquareDartEndpoint n x := by
  cases ht : (fkIsingSquareSideCorner x.2).2 <;>
    simp [fkIsingSquareBondMate, ht]

theorem fkIsingSquareNextDirection_ne (n : Nat) (_hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareNextDirection n u d ≠ d := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquareNextDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable]

theorem fkIsingSquarePreviousDirection_ne (n : Nat) (_hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquarePreviousDirection n u d ≠ d := by
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  cases d <;>
    by_cases he : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hnorth : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hw : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hs : fkIsingSquareDirectionAvailable n u .south <;>
    simp only [fkIsingSquarePreviousDirection, he, hnorth, hw, hs] <;>
    simp_all [fkIsingSquareDirectionAvailable]

theorem fkIsingSquareNeighbor_ne (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareNeighbor n u d hd ≠ u :=
  (fkIsingSquare_adj_neighbor n u d hd).ne'

theorem fkIsingSquareNeighbor_injective (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d e : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e)
    (h : fkIsingSquareNeighbor n u d hd =
      fkIsingSquareNeighbor n u e he) : d = e := by
  have hv := congrArg Subtype.val h
  cases d <;> cases e <;>
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hv ⊢

theorem fkIsingSquareDirectionEdge_injective (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d e : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e)
    (h : fkIsingSquareDirectionEdge n u d hd =
      fkIsingSquareDirectionEdge n u e he) : d = e := by
  have hs : s(u, fkIsingSquareNeighbor n u d hd) =
      s(u, fkIsingSquareNeighbor n u e he) := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp hs with hsame | hswap
  · exact fkIsingSquareNeighbor_injective n u d e hd he hsame.2
  · exact False.elim
      ((fkIsingSquareNeighbor_ne n u e he) hswap.1.symm)

theorem fkIsingSquareBondMate_edge_ne (n : Nat) (hn : 0 < n)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareBondMate n hn x).1 ≠ x.1 := by
  intro h
  cases ht : (fkIsingSquareSideCorner x.2).2
  · simp only [fkIsingSquareBondMate, ht,
      fkIsingSquareDirectionDart] at h
    rw [← fkIsingSquareDirectionEdge_reconstruct n x] at h
    exact fkIsingSquareNextDirection_ne n hn _ _
      (fkIsingSquareDartDirection_available n x)
      (fkIsingSquareDirectionEdge_injective n _ _ _ _ _ h)
  · simp only [fkIsingSquareBondMate, ht,
      fkIsingSquareDirectionDart] at h
    rw [← fkIsingSquareDirectionEdge_reconstruct n x] at h
    exact fkIsingSquarePreviousDirection_ne n hn _ _
      (fkIsingSquareDartDirection_available n x)
      (fkIsingSquareDirectionEdge_injective n _ _ _ _ _ h)

theorem fkIsingSquareBondMate_ne (n : Nat) (hn : 0 < n)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareBondMate n hn x ≠ x := by
  intro h
  exact fkIsingSquareBondMate_edge_ne n hn x (congrArg Prod.fst h)

theorem fkIsingSquareBondMate_cornerTurn_ne (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner (fkIsingSquareBondMate n hn d).2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  cases ht : (fkIsingSquareSideCorner d.2).2 <;>
    simp [fkIsingSquareBondMate, ht, fkIsingSquareDirectionDart_turn]

theorem fkIsingSquareBondMate_ne_localMate (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareBondMate n hn x ≠
      FKIsingMedialDart.localMate omega x := by
  intro h
  apply fkIsingSquareBondMate_edge_ne n hn x
  have hf := congrArg Prod.fst h
  rcases x with ⟨e, side⟩
  cases ho : omega e.1 <;> cases side <;>
    simpa [FKIsingMedialDart.localMate, ho] using hf


end
end StatMech.Universality
