/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part8


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredLoopGraph (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareWiredCarrier n) where
  Adj x y :=
    (x ≠ .source ∧ x ≠ .terminal ∧
      y = fkIsingSquareWiredIncidenceMate n x) ∨
    y = fkIsingSquareWiredTransitionMate n hn omega x
  symm := by
    constructor
    intro x y h
    rcases h with ⟨hxs, hxt, rfl⟩ | rfl
    · left
      cases x <;> simp_all [fkIsingSquareWiredIncidenceMate]
    · right
      exact (fkIsingSquareWiredTransitionMate_involutive n hn omega x).symm
  loopless := ⟨by
    intro x h
    rcases h with ⟨hxs, hxt, h⟩ | h
    · cases x with
      | source => exact hxs rfl
      | terminal => exact hxt rfl
      | dart d => simp [fkIsingSquareWiredIncidenceMate] at h
      | bond d => simp [fkIsingSquareWiredIncidenceMate] at h
    · exact fkIsingSquareWiredTransitionMate_ne n hn omega x h.symm⟩

end
end StatMech.Universality
