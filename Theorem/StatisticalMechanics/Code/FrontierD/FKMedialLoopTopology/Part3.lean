/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part3
open SimpleGraph


namespace StatMech.FrontierD

theorem fkMedialDartIncoming_localMate_ne
    (pairing : FKMedialLoopPairing T) (omega : SixVertexArrows T)
    (hcompat : forall v,
      fkLoopPairingCompatible (pairing v) omega v)
    (d : FKMedialDart T) :
    fkMedialDartIncoming omega (fkMedialLocalMate pairing d) ≠
      fkMedialDartIncoming omega d := by
  rcases d with ⟨v, side⟩
  have h := hcompat v
  cases hp : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, fkMedialDartIncoming,
      fkLoopPairingCompatible, hp] at h ⊢ <;> tauto


theorem fkMedialDartIncoming_bondMate_ne
    (T : EvenTorus) (omega : SixVertexArrows T)
    (d : FKMedialDart T) :
    fkMedialDartIncoming omega (fkMedialBondMate T d) ≠
      fkMedialDartIncoming omega d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side
  · simp [fkMedialBondMate, fkMedialDartIncoming,
      fkLoopWestIncoming, fkLoopEastIncoming]
  · simp [fkMedialBondMate, fkMedialDartIncoming,
      fkLoopWestIncoming, fkLoopEastIncoming,
      svCyclicPred_finitePeriodicSucc]
  · simp [fkMedialBondMate, fkMedialDartIncoming,
      fkLoopSouthIncoming, fkLoopNorthIncoming]
  · simp [fkMedialBondMate, fkMedialDartIncoming,
      fkLoopSouthIncoming, fkLoopNorthIncoming,
      svCyclicPred_finitePeriodicSucc]


theorem fkMedialLoopGraph_adj_incoming_ne
    (pairing : FKMedialLoopPairing T) (omega : SixVertexArrows T)
    (hcompat : forall v,
      fkLoopPairingCompatible (pairing v) omega v)
    {d e : FKMedialDart T} (hde : (fkMedialLoopGraph T pairing).Adj d e) :
    fkMedialDartIncoming omega d ≠ fkMedialDartIncoming omega e := by
  rcases hde with (rfl | h) | (rfl | h)
  · exact (fkMedialDartIncoming_localMate_ne
      pairing omega hcompat d).symm
  · subst d
    exact fkMedialDartIncoming_localMate_ne pairing omega hcompat e
  · exact (fkMedialDartIncoming_bondMate_ne T omega d).symm
  · subst d
    exact fkMedialDartIncoming_bondMate_ne T omega e


end StatMech.FrontierD
