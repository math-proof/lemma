/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc43reimer.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc44boxineq.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc44_diagonalSlab_charge_fails_fin3 :
    ({1} : Finset (Fin 3)) ∈ rc44_famCylBoxEComp {0, 1}
        (rc44_slab0 2 rc44_Aref) (rc44_slab0 2 rc44_Bref)
      ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1}
          (rc44_slab0 2 rc44_Aref) (rc44_slab1 2 rc44_Bref)
      ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1}
          (rc44_slab1 2 rc44_Aref) (rc44_slab0 2 rc44_Bref) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rc44_Aref, rc44_Bref, rc44_slab0, rc44_slab0]; decide
  · rw [rc44_Aref, rc44_Bref, rc44_slab0, rc44_slab1]; decide
  · rw [rc44_Aref, rc44_Bref, rc44_slab1, rc44_slab0]; decide


end StatMech.Walls
