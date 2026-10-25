/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift


namespace StatMech.FrontierD

def fkRectMedialDualShiftDartEquiv (R : FKRectTorus) :
    FKMedialDart R.medialTorus ≃ FKMedialDart R.medialTorus where
  toFun := fkRectMedialDualShiftDart R
  invFun := fkRectMedialDualUnshiftDart R
  left_inv := fkRectMedialDualUnshiftDart_shift R
  right_inv := fkRectMedialDualShiftDart_unshift R


end StatMech.FrontierD
