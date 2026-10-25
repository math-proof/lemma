/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoStepCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourWeightedConvolution
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourDynamicCount
open Finset


namespace StatMech.FrontierD

theorem sixVertexFourGradeCountExecutable_eq_cycleTuple
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourCycleTupleGradeCount sector totalC := by
  unfold sixVertexMarkedSectorRowCycleGradeCountExecutable
    sixVertexFourCycleTupleGradeCount
  apply Fintype.sum_equiv (piFinFourCycleEquiv (SixVertexRow 4))
  intro vertical
  simp only [Equiv.symm_apply_apply]
  rfl

theorem sixVertexFourCycleTupleGradeCount_eq_rows
    (sector : Fin 5) (totalC : Nat) :
    sixVertexFourCycleTupleGradeCount sector totalC =
      sixVertexFourCycleRowGradeCount sector totalC := by
  unfold sixVertexFourCycleTupleGradeCount sixVertexFourCycleRowGradeCount
  simp only [Fintype.sum_prod_type, piFinFourCycleEquiv,
    Equiv.coe_fn_symm_mk, sixVertexFourByFourVertical_last]

theorem sixVertexFourGradeCountExecutable_eq_cycleRows
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourCycleRowGradeCount sector totalC :=
  (sixVertexFourGradeCountExecutable_eq_cycleTuple sector totalC).trans
    (sixVertexFourCycleTupleGradeCount_eq_rows sector totalC)

end StatMech.FrontierD
