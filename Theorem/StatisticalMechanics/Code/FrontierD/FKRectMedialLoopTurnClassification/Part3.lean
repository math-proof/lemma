/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part2
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

open FKMedialTurningFiber

noncomputable section

variable {T : EvenTorus}

theorem fkRectBlackOrbitList_mem_self
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    d ∈ fkRectBlackOrbitList pairing d := by
  rw [fkRectBlackOrbitList, Equiv.Perm.mem_toList_iff]
  exact ⟨Equiv.Perm.SameCycle.refl _ _, by
    rw [Equiv.Perm.mem_support]
    exact fkMedialBlackBoundaryPerm_apply_ne pairing d⟩

theorem fkRectBlackOrbitList_length_pos
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    0 < (fkRectBlackOrbitList pairing d).length := by
  by_contra h
  have hzero : (fkRectBlackOrbitList pairing d).length = 0 := by omega
  have hnil : fkRectBlackOrbitList pairing d = [] :=
    List.eq_nil_of_length_eq_zero hzero
  have hmem := fkRectBlackOrbitList_mem_self pairing d
  rw [hnil] at hmem
  simp at hmem

theorem fkRectBlackOrbitList_get
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (i : Fin (fkRectBlackOrbitList pairing d).length) :
    (fkRectBlackOrbitList pairing d).get i =
      (fkMedialBlackBoundaryPerm pairing)^[i.val] d := by
  change (fkRectBlackOrbitList pairing d).get i =
    ((fkMedialBlackBoundaryPerm pairing) ^ i.val) d
  simpa [fkRectBlackOrbitList, List.get_eq_getElem] using
    Equiv.Perm.getElem_toList (fkMedialBlackBoundaryPerm pairing)
      d i.val i.isLt

end
end StatMech.FrontierD
