/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Instance.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology
open SimpleGraph


namespace StatMech.FrontierD

theorem fkMedialLoopGraph_adj_iff
    (T : EvenTorus) (pairing : FKMedialLoopPairing T)
    (d e : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).Adj d e ↔
      e = fkMedialLocalMate pairing d ∨ e = fkMedialBondMate T d := by
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl h
    · left
      rw [h, fkMedialLocalMate_involutive]
    · exact Or.inr h
    · right
      rw [h, fkMedialBondMate_involutive]
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)

theorem fkMedialLocalMate_ne_bondMate
    (T : EvenTorus) (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    fkMedialLocalMate pairing d ≠ fkMedialBondMate T d := by
  rcases d with ⟨v, side⟩
  cases hp : pairing v <;> cases side <;>
    simp [fkMedialLocalMate, fkMedialBondMate, hp]

theorem fkMedialLoopGraph_neighborFinset
    (T : EvenTorus) (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).neighborFinset d =
      {fkMedialLocalMate pairing d, fkMedialBondMate T d} := by
  ext e
  rw [SimpleGraph.mem_neighborFinset, fkMedialLoopGraph_adj_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]


theorem fkMedialLoopGraph_degree_eq_two
    (T : EvenTorus) (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).degree d = 2 := by
  rw [<- SimpleGraph.card_neighborFinset_eq_degree,
    fkMedialLoopGraph_neighborFinset]
  simp [fkMedialLocalMate_ne_bondMate T pairing d]


end StatMech.FrontierD
