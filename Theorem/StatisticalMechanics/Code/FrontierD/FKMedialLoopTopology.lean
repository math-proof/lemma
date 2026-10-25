/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology
open SimpleGraph


namespace StatMech.FrontierD

theorem finitePeriodicSucc_cyclicPred {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    finitePeriodicSucc hN (SixVertexArrows.cyclicPred hN i) = i := by
  obtain ⟨j, hj⟩ := (svFinitePeriodicSuccEquiv hN).surjective i
  change finitePeriodicSucc hN j = i at hj
  rw [<- hj, svCyclicPred_finitePeriodicSucc]

theorem fkMedialLocalMate_involutive
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    fkMedialLocalMate pairing (fkMedialLocalMate pairing d) = d := by
  rcases d with ⟨v, side⟩
  cases h : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, h]

theorem fkMedialBondMate_involutive
    (T : EvenTorus) (d : FKMedialDart T) :
    fkMedialBondMate T (fkMedialBondMate T d) = d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side
  · simp [fkMedialBondMate, finitePeriodicSucc_cyclicPred]
  · simp [fkMedialBondMate, svCyclicPred_finitePeriodicSucc]
  · simp [fkMedialBondMate, finitePeriodicSucc_cyclicPred]
  · simp [fkMedialBondMate, svCyclicPred_finitePeriodicSucc]

theorem fkMedialLocalMate_ne
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    fkMedialLocalMate pairing d ≠ d := by
  rcases d with ⟨v, side⟩
  cases h : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, h]

theorem fkMedialBondMate_ne (T : EvenTorus) (d : FKMedialDart T) :
    fkMedialBondMate T d ≠ d := by
  rcases d with ⟨v, side⟩
  cases side <;> simp [fkMedialBondMate]


end StatMech.FrontierD
