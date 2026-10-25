/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPathSplice.Part2
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredIncidenceGraph (n : Nat) :
    SimpleGraph (FKIsingSquareWiredCarrier n) where
  Adj x y := x ≠ .source ∧ x ≠ .terminal ∧
    y = fkIsingSquareWiredIncidenceMate n x
  symm := by
    constructor
    rintro x _ ⟨hxs, hxt, rfl⟩
    cases x with
    | source => exact False.elim (hxs rfl)
    | terminal => exact False.elim (hxt rfl)
    | dart d => simp [fkIsingSquareWiredIncidenceMate]
    | bond d => simp [fkIsingSquareWiredIncidenceMate]
  loopless := ⟨by
    rintro x ⟨hxs, hxt, hx⟩
    cases x with
    | source => exact hxs rfl
    | terminal => exact hxt rfl
    | dart d => simp [fkIsingSquareWiredIncidenceMate] at hx
    | bond d => simp [fkIsingSquareWiredIncidenceMate] at hx⟩

end
end StatMech.Universality
