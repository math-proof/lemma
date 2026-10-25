/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential.Part4
open scoped BigOperators
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Onsager

@[simp] theorem zmodFinEquiv_two_apply (a : Fin 2) :
    (ZMod.finEquiv 2) a = (a : ZMod 2) := rfl

theorem finTwo_add_self_eq_zero (a : Fin 2) : a + a = 0 := by
  apply Fin.ext
  simp only [Fin.val_add, Fin.val_zero]
  omega


end StatMech.FrontierA
