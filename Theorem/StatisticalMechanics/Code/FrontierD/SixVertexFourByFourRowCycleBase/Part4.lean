/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourGradeCountExecutable_eq_tuple
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourTupleGradeCountExecutable sector totalC := by
  unfold sixVertexMarkedSectorRowCycleGradeCountExecutable
    sixVertexFourByFourTupleGradeCountExecutable
  apply Fintype.sum_equiv (piFinFourEquiv (SixVertexRow 4))
  intro vertical
  simp only [Equiv.symm_apply_apply]
  rfl

theorem sixVertexFourByFourTupleGradeCountExecutable_eq_rows
    (sector : Fin 5) (totalC : Nat) :
    sixVertexFourByFourTupleGradeCountExecutable sector totalC =
      sixVertexFourByFourRowCycleGradeCountExecutable sector totalC := by
  unfold sixVertexFourByFourTupleGradeCountExecutable
    sixVertexFourByFourRowCycleGradeCountExecutable
  simp only [Fintype.sum_prod_type, piFinFourEquiv, Equiv.coe_fn_symm_mk]

theorem sixVertexFourByFourGradeCountExecutable_eq_rows
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourRowCycleGradeCountExecutable sector totalC :=
  (sixVertexFourByFourGradeCountExecutable_eq_tuple sector totalC).trans
    (sixVertexFourByFourTupleGradeCountExecutable_eq_rows sector totalC)

end
end StatMech.FrontierD
