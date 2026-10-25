/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift


namespace StatMech.FrontierD

@[simp] theorem fkRectMedialDualUnshiftVertex_shift
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectMedialDualUnshiftVertex R (fkRectMedialDualShiftVertex R v) = v := by
  rcases v with ⟨i, j⟩
  simp [fkRectMedialDualUnshiftVertex, fkRectMedialDualShiftVertex,
    finitePeriodicSucc_cyclicPred]

@[simp] theorem fkRectMedialDualShiftVertex_unshift
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectMedialDualShiftVertex R (fkRectMedialDualUnshiftVertex R v) = v := by
  rcases v with ⟨i, j⟩
  simp [fkRectMedialDualUnshiftVertex, fkRectMedialDualShiftVertex,
    svCyclicPred_finitePeriodicSucc]

@[simp] theorem fkRectMedialDualUnshiftDart_shift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectMedialDualUnshiftDart R (fkRectMedialDualShiftDart R d) = d := by
  rcases d with ⟨v, side⟩
  simp [fkRectMedialDualUnshiftDart, fkRectMedialDualShiftDart]

@[simp] theorem fkRectMedialDualShiftDart_unshift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectMedialDualShiftDart R (fkRectMedialDualUnshiftDart R d) = d := by
  rcases d with ⟨v, side⟩
  simp [fkRectMedialDualUnshiftDart, fkRectMedialDualShiftDart]


end StatMech.FrontierD
