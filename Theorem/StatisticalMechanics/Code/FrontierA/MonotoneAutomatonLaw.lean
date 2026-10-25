/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteBond.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw
open MeasureTheory
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


@[simp] theorem fieldShift_apply (g : Multiplicative (Site d))
    (xi : NonnegativeField d) (x : Site d) :
    fieldShift g xi x = xi (g⁻¹ • x) :=
  rfl

@[simp] theorem fieldShift_one :
    (fieldShift (1 : Multiplicative (Site d)) :
      NonnegativeField d → NonnegativeField d) = id := by
  funext xi x
  simp [fieldShift]

theorem fieldShift_mul (g h : Multiplicative (Site d)) :
    (fieldShift (g * h) : NonnegativeField d → NonnegativeField d) =
      fieldShift g ∘ fieldShift h := by
  funext xi x
  simp [fieldShift, mul_smul]

theorem measurable_fieldShift (g : Multiplicative (Site d)) :
    Measurable (fieldShift g : NonnegativeField d → NonnegativeField d) :=
  measurable_pi_lambda _ fun x => measurable_pi_apply (g⁻¹ • x)


end StatMech.FrontierA
