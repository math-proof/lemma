/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPathSplice
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredLoopGraph_adj_phase_succ
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    fkIsingSquareWiredCarrierPhase n y =
      fkIsingSquareWiredCarrierPhase n x + 1 ∨
    fkIsingSquareWiredCarrierPhase n x =
      fkIsingSquareWiredCarrierPhase n y + 1 := by
  rcases hxy with hinc | htrans
  · rcases hinc with ⟨hxs, hxt, rfl⟩
    cases x with
    | source => exact False.elim (hxs rfl)
    | terminal => exact False.elim (hxt rfl)
    | dart d =>
        cases hcorner : (fkIsingSquareSideCorner d.2).2 <;>
          simp [fkIsingSquareWiredCarrierPhase,
            fkIsingSquareWiredIncidenceMate, hcorner]
    | bond d =>
        cases hcorner : (fkIsingSquareSideCorner d.2).2 <;>
          simp [fkIsingSquareWiredCarrierPhase,
            fkIsingSquareWiredIncidenceMate, hcorner]
  · subst y
    cases x with
    | source =>
        simp [fkIsingSquareWiredCarrierPhase,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredBoundaryDart]
    | terminal =>
        simp [fkIsingSquareWiredCarrierPhase,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTerminalDart,
          fkIsingSquareWiredBoundaryDart]
    | dart d =>
        have hne := fkIsingSquare_localMate_cornerTurn_ne n omega d
        cases hd : (fkIsingSquareSideCorner d.2).2 <;>
          cases hm : (fkIsingSquareSideCorner
            (FKIsingMedialDart.localMate omega d).2).2 <;>
          simp_all [fkIsingSquareWiredCarrierPhase,
            fkIsingSquareWiredTransitionMate]
    | bond d =>
        by_cases hs : d = fkIsingSquareWiredSourceDart n hn
        · subst d
          simp [fkIsingSquareWiredCarrierPhase, fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredSourceDart,
            fkIsingSquareWiredBoundaryDart]
        by_cases ht : d = fkIsingSquareWiredTerminalDart n hn
        · subst d
          left
          simp only [fkIsingSquareWiredTransitionMate]
          rw [if_neg hs]
          simp only [if_true]
          simp [fkIsingSquareWiredCarrierPhase,
            fkIsingSquareWiredTerminalDart,
            fkIsingSquareWiredBoundaryDart]
        · have hne := fkIsingSquareWiredBondMate_cornerTurn_ne n hn d
          cases hd : (fkIsingSquareSideCorner d.2).2 <;>
            cases hm : (fkIsingSquareSideCorner
              (fkIsingSquareWiredBondMate n hn d).2).2 <;>
            simp_all [fkIsingSquareWiredCarrierPhase,
              fkIsingSquareWiredTransitionMate, hs, ht]


end
end StatMech.Universality
