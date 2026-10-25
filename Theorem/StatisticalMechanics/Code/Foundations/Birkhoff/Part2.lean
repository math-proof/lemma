/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Birkhoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Foundations.Birkhoff.Part2
open MeasureTheory Filter Finset Function
open scoped Topology


namespace StatMech

namespace Birkhoff

variable {α : Type*} {T : α → α} {f : α → ℝ}


section MeasureTheory

variable [MeasurableSpace α] {μ : Measure α}


variable [IsFiniteMeasure μ]


theorem hopf_maximal_inequality (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (a : ℝ)
    (n : ℕ) :
    a * (μ (maximalLevelSet T f a n)).toReal ≤ ∫ x in maximalLevelSet T f a n, f x ∂μ := by
  have hfa : Integrable (fun y => f y - a) μ := hf.sub (integrable_const a)
  
  have hmax : (0 : ℝ) ≤ ∫ x in maximalLevelSet T f a n, (f x - a) ∂μ :=
    maximal_ergodic_inequality hT hfa n
  
  have hsplit : ∫ x in maximalLevelSet T f a n, (f x - a) ∂μ
      = (∫ x in maximalLevelSet T f a n, f x ∂μ) - a * (μ (maximalLevelSet T f a n)).toReal := by
    rw [integral_sub hf.integrableOn (integrable_const a).integrableOn, setIntegral_const,
      smul_eq_mul, mul_comm, Measure.real]
  rw [hsplit] at hmax
  linarith

end MeasureTheory
end Birkhoff
end StatMech
