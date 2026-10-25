/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part19


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredPhysicalBlackOfDart_bijective (n : Nat) :
    Function.Bijective (fkIsingSquareWiredPhysicalBlackOfDart n) := by
  constructor
  · intro d f h
    rcases d with ⟨e, side⟩
    rcases f with ⟨f, side'⟩
    have hval := congrArg (fun x : FKIsingSquareWiredPhysicalBlackCarrier n =>
      x.1.1) h
    cases side <;> cases side' <;>
      simpa [fkIsingSquareWiredPhysicalBlackOfDart,
        fkIsingSquareWiredBlackOfDart] using hval
  · rintro ⟨⟨x, hblack⟩, hterminal⟩
    cases x with
    | source =>
        simp [fkIsingSquareWiredCarrierColor] at hblack
    | terminal =>
        exact False.elim (hterminal rfl)
    | dart d =>
        rcases d with ⟨e, side⟩
        cases side with
        | west =>
            refine ⟨(e, .west), ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl
        | east =>
            refine ⟨(e, .east), ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl
        | south =>
            simp [fkIsingSquareWiredCarrierColor,
              fkIsingSquareWiredDartSideColor] at hblack
        | north =>
            simp [fkIsingSquareWiredCarrierColor,
              fkIsingSquareWiredDartSideColor] at hblack
    | bond d =>
        rcases d with ⟨e, side⟩
        cases side with
        | west =>
            simp [fkIsingSquareWiredCarrierColor,
              fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner] at hblack
        | east =>
            simp [fkIsingSquareWiredCarrierColor,
              fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner] at hblack
        | south =>
            refine ⟨(e, .south), ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl
        | north =>
            refine ⟨(e, .north), ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl

theorem fkIsingSquareWiredBlackOfDart_injective (n : Nat) :
    Function.Injective (fkIsingSquareWiredBlackOfDart n) := by
  intro d f h
  apply (fkIsingSquareWiredPhysicalBlackOfDart_bijective n).1
  apply Subtype.ext
  exact h


end
end StatMech.Universality
