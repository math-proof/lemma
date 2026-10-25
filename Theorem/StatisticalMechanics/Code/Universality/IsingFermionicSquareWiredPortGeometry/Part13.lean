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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part13


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredExpandedBulgeMidpoint_injective
    (n : Nat) (hn : 0 < n) :
    Function.Injective (fun x : Fin (2 * n) × Fin 3 =>
      fkIsingSquareWiredExpandedBulgeMidpoint n hn x.1 x.2) := by
  rintro ⟨k, a⟩ ⟨l, b⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases a <;> fin_cases b <;>
    simp [fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEndpoints,
      fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedStart,
      fkIsingSquareWiredExpandedMiddle,
      fkIsingSquareWiredExpandedEnd,
      fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper] at hx hy
  all_goals try omega
  all_goals
    have hkl : k = l := Fin.ext (by omega)
    subst l
    rfl

set_option maxHeartbeats 1000000 in


theorem fkIsingSquareWiredSlotLocalBulge_midpoint_ne
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Fin (2 * n)) (j : Fin 3) :
    fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) +
          fkIsingSquareWiredSlotIntPosition n
            (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega d)) ≠
        fkIsingSquareWiredExpandedBulgeMidpoint n hn k j := by
  intro hmid
  rw [fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot] at hmid
  have hx := congrArg Prod.fst hmid
  have hy := congrArg Prod.snd hmid
  rcases d with ⟨e, side⟩
  have bt0 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).tail 0
  have bt1 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).tail 1
  cases haxis : (fkIsingSquareOrientedEdge n e).axis
  all_goals
    cases homega : omega e.1 <;> cases side <;> fin_cases j <;>
    simp only [FKIsingMedialDart.localMate, homega] at hx hy <;>
    simp [fkIsingSquareWiredPortIntPosition,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEndpoints,
      fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedStart,
      fkIsingSquareWiredExpandedMiddle,
      fkIsingSquareWiredExpandedEnd,
      fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper,
      haxis] at hx hy <;>
    omega


end
end StatMech.Universality
