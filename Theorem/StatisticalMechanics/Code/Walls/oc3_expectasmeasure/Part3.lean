/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.Walls.oc3_vcubeprob
import Instance.StatisticalMechanics.Code.Walls.oc3_expectasmeasure.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory
open StatMech.OSSS

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc3_pwMeasure_singleton (ν : E → Bool → ℝ) (hν : IsProbWeight ν) (ω : ConfigSpace E) :
    oc3_pwMeasure ν hν {ω} = ∏ e, ENNReal.ofReal (ν e (ω e)) := by
  unfold oc3_pwMeasure
  rw [Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun e _ => oc3_siteMeasure_singleton ν hν e (ω e))


theorem oc3_pwMeasure_real_singleton (ν : E → Bool → ℝ) (hν : IsProbWeight ν)
    (ω : ConfigSpace E) :
    (oc3_pwMeasure ν hν).real {ω} = weight ν ω := by
  rw [Measure.real, oc3_pwMeasure_singleton, ENNReal.toReal_prod]
  unfold weight
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [ENNReal.toReal_ofReal (hν.nonneg e (ω e))]


theorem oc3_expect_eq_integral (ν : E → Bool → ℝ) (hν : IsProbWeight ν)
    (g : ConfigSpace E → ℝ) :
    expect ν g = ∫ ω, g ω ∂(oc3_pwMeasure ν hν) := by
  rw [integral_fintype (Integrable.of_finite)]
  unfold OSSS.expect
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [oc3_pwMeasure_real_singleton ν hν ω, smul_eq_mul, mul_comm]


theorem oc3_integral_one (ν : E → Bool → ℝ) (hν : IsProbWeight ν) :
    ∫ _ω, (1 : ℝ) ∂(oc3_pwMeasure ν hν) = 1 := by
  rw [integral_const, probReal_univ, smul_eq_mul, mul_one]


theorem oc3_expect_const_eq_integral (ν : E → Bool → ℝ) (hν : IsProbWeight ν) :
    expect ν (fun _ => (1 : ℝ)) = 1 := by
  rw [oc3_expect_eq_integral ν hν (fun _ => 1), oc3_integral_one ν hν]


end Walls
end StatMech
