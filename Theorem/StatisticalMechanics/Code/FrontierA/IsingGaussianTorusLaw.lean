/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part4
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusLaw
open Finset MeasureTheory
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising

noncomputable section

variable {d k : Nat}


theorem isingTorusZeroFieldMass_nonneg (beta : Real) :
    0 <= isingTorusZeroFieldMass (d := d) (k := k) beta := by
  intro sigma
  exact div_nonneg (Real.exp_pos _).le
    (isingTorusShiftedPartition_zero_pos beta).le

theorem sum_isingTorusZeroFieldMass (beta : Real) :
    ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
      isingTorusZeroFieldMass beta sigma = 1 := by
  have hZ := isingTorusShiftedPartition_zero_pos
    (d := d) (k := k) beta
  unfold isingTorusZeroFieldMass isingTorusShiftedPartition
  rw [← Finset.sum_div Finset.univ]
  simp only [add_zero]
  apply div_self
  simpa only [isingTorusShiftedPartition, Pi.zero_apply, add_zero] using hZ.ne'


end
end StatMech.FrontierA
