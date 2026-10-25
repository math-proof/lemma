/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VectorTwoPoint
import Theorem.StatisticalMechanics.Code.Probability.KKLInequality.Part4
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Def.StatisticalMechanics.Code.Probability.KKLfromHC.Part5
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem khc_logSobolevStep_zero : khc_LogSobolevStep 0 := by
  intro E _ _ _ φ _
  rw [zero_mul, zero_mul]
  rw [← khc_totalInfl_eq_fourierWeight φ]
  exact kkl_totalInfl_nonneg
    (OSSS.bernoulliWeight_isProbWeight (by norm_num) (by norm_num)) _


theorem khc_KKL {c : ℝ} (H : khc_LogSobolevStep c) :
    KKLHypercontractive (1 / 2 : ℝ) c := by
  intro E _ _ _ φ
  
  rw [show OSSS.var (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
        = ∑ S ∈ (univ.erase (∅ : Finset E)),
            (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      from khc_var_eq_fourierWeight _]
  rw [show totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
        = ∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      from khc_totalInfl_eq_fourierWeight _]
  
  exact H φ (fun ρ h0 h1 => khc_lowDegreeWeight_le h0 h1 _)

end Probability
end StatMech
