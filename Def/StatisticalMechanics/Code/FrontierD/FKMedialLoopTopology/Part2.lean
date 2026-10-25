/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology
open SimpleGraph


namespace StatMech.FrontierD

def fkMedialLoopGraph (T : EvenTorus)
    (pairing : FKMedialLoopPairing T) : SimpleGraph (FKMedialDart T) where
  Adj d e :=
    (e = fkMedialLocalMate pairing d ∨ d = fkMedialLocalMate pairing e) ∨
      (e = fkMedialBondMate T d ∨ d = fkMedialBondMate T e)
  symm := by
    constructor
    intro d e h
    rcases h with (h | h) | (h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := ⟨by
    intro d h
    rcases h with (h | h) | (h | h)
    · exact fkMedialLocalMate_ne pairing d h.symm
    · exact fkMedialLocalMate_ne pairing d h.symm
    · exact fkMedialBondMate_ne T d h.symm
    · exact fkMedialBondMate_ne T d h.symm⟩

end StatMech.FrontierD
