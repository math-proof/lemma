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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part19


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareDirectionDart_endpoint (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareDartEndpoint n
      (fkIsingSquareDirectionDart n u d hd turn) = u := by
  unfold fkIsingSquareDirectionDart fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases d <;> cases turn <;> rfl

@[simp] theorem fkIsingSquareDirectionDart_direction (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareDartDirection n
      (fkIsingSquareDirectionDart n u d hd turn) = d := by
  unfold fkIsingSquareDirectionDart fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  cases d <;> cases turn <;> rfl

@[simp] theorem fkIsingSquareDirectionDart_turn (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    (fkIsingSquareSideCorner
      (fkIsingSquareDirectionDart n u d hd turn).2).2 = turn := by
  cases d <;> cases turn <;> rfl

theorem fkIsingSquareDirectionDart_congr (n : Nat)
    (u : (fkSquareBoxPlanar n).V) {d e : FKIsingSquareDirection}
    (h : d = e) (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e)
    (turn : FKIsingSquareCornerTurn) :
    fkIsingSquareDirectionDart n u d hd turn =
      fkIsingSquareDirectionDart n u e he turn := by
  subst e
  rfl


theorem fkIsingSquareDirectionEdge_reconstruct (n : Nat)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDirectionEdge n (fkIsingSquareDartEndpoint n x)
      (fkIsingSquareDartDirection n x)
      (fkIsingSquareDartDirection_available n x) = x.1 := by
  rcases x with ⟨e, side⟩
  apply Subtype.ext
  rw [← fkIsingSquareOrientedEdge_eq n e]
  have step := (fkIsingSquareOrientedEdge n e).step
  cases haxis : (fkIsingSquareOrientedEdge n e).axis
  · simp [haxis] at step
    have haE : fkIsingSquareDirectionAvailable n
        (fkIsingSquareOrientedEdge n e).tail .east := by
      simpa [fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .west)
    have haW : fkIsingSquareDirectionAvailable n
        (fkIsingSquareOrientedEdge n e).head .west := by
      simpa [fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .east)
    have hE : fkIsingSquareNeighbor n
        (fkIsingSquareOrientedEdge n e).tail .east haE =
        (fkIsingSquareOrientedEdge n e).head := by
      apply Subtype.ext
      change (fkIsingSquareOrientedEdge n e).tail.1 + ![1, 0] =
        (fkIsingSquareOrientedEdge n e).head.1
      rw [step]
      funext i
      fin_cases i <;> simp [Pi.add_apply] <;> rfl
    have hW : fkIsingSquareNeighbor n
        (fkIsingSquareOrientedEdge n e).head .west haW =
        (fkIsingSquareOrientedEdge n e).tail := by
      apply Subtype.ext
      change (fkIsingSquareOrientedEdge n e).head.1 + ![-1, 0] =
        (fkIsingSquareOrientedEdge n e).tail.1
      rw [step]
      funext i
      fin_cases i <;> simp [Pi.add_apply] <;> rfl
    cases side <;> simp [fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      fkIsingSquareDirectionEdge, hE, hW]
  · simp [haxis] at step
    have haN : fkIsingSquareDirectionAvailable n
        (fkIsingSquareOrientedEdge n e).tail .north := by
      simpa [fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .west)
    have haS : fkIsingSquareDirectionAvailable n
        (fkIsingSquareOrientedEdge n e).head .south := by
      simpa [fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .east)
    have hN : fkIsingSquareNeighbor n
        (fkIsingSquareOrientedEdge n e).tail .north haN =
        (fkIsingSquareOrientedEdge n e).head := by
      apply Subtype.ext
      change (fkIsingSquareOrientedEdge n e).tail.1 + ![0, 1] =
        (fkIsingSquareOrientedEdge n e).head.1
      rw [step]
      funext i
      fin_cases i <;> simp [Pi.add_apply] <;> rfl
    have hS : fkIsingSquareNeighbor n
        (fkIsingSquareOrientedEdge n e).head .south haS =
        (fkIsingSquareOrientedEdge n e).tail := by
      apply Subtype.ext
      change (fkIsingSquareOrientedEdge n e).head.1 + ![0, -1] =
        (fkIsingSquareOrientedEdge n e).tail.1
      rw [step]
      funext i
      fin_cases i <;> simp [Pi.add_apply] <;> rfl
    cases side <;> simp [fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      fkIsingSquareDirectionEdge, hN, hS]


theorem fkIsingSquareDirectionDart_reconstruct (n : Nat)
    (x : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDirectionDart n (fkIsingSquareDartEndpoint n x)
      (fkIsingSquareDartDirection n x)
      (fkIsingSquareDartDirection_available n x)
      (fkIsingSquareSideCorner x.2).2 = x := by
  apply Prod.ext
  · exact fkIsingSquareDirectionEdge_reconstruct n x
  · rcases x with ⟨e, side⟩
    cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
      cases side <;>
      simp [fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis] <;> rfl


end
end StatMech.Universality
