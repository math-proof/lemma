/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Def.StatisticalMechanics.Code.OSSS.Lindeberg
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace Lindeberg

open OSSS.Monotonic OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma mean_add (μ : ConfigSpace E → ℝ) (g h : ConfigSpace E → ℝ) :
    mean μ (fun ω => g ω + h ω) = mean μ g + mean μ h := by
  unfold mean; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring)

lemma mean_sub (μ : ConfigSpace E → ℝ) (g h : ConfigSpace E → ℝ) :
    mean μ (fun ω => g ω - h ω) = mean μ g - mean μ h := by
  unfold mean; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun ω _ => by ring)

lemma mean_const_mul (μ : ConfigSpace E → ℝ) (c : ℝ) (g : ConfigSpace E → ℝ) :
    mean μ (fun ω => c * g ω) = c * mean μ g := by
  unfold mean; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma mean_const (μ : ConfigSpace E → ℝ) (hμ : ∑ ω, μ ω = 1) (c : ℝ) :
    mean μ (fun _ => c) = c := by
  unfold mean
  simp only []
  rw [← Finset.mul_sum, hμ, mul_one]


lemma var_eq_double_sum (μ : ConfigSpace E → ℝ) (hμ : ∑ ω, μ ω = 1) (f : ConfigSpace E → ℝ) :
    var μ f = (1 / 2) * ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2 := by
  unfold var cov mean
  have hsplit : ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2
      = ∑ x, ∑ y, ((f x * f x) * μ x * μ y)
        + ∑ x, ∑ y, ((f y * f y) * μ x * μ y)
        - 2 * ∑ x, ∑ y, ((f x * μ x) * (f y * μ y)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro y _; ring
  rw [hsplit]
  have h1 : ∑ x, ∑ y, ((f x * f x) * μ x * μ y) = ∑ x, (f x * f x) * μ x := by
    apply Finset.sum_congr rfl; intro x _; rw [← Finset.mul_sum, hμ, mul_one]
  have h2 : ∑ x, ∑ y, ((f y * f y) * μ x * μ y) = ∑ y, (f y * f y) * μ y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y _
    rw [show (fun x => (f y * f y) * μ x * μ y) = (fun x => ((f y * f y) * μ y) * μ x) from by
          funext x; ring, ← Finset.mul_sum, hμ, mul_one]
  have h3 : ∑ x, ∑ y, ((f x * μ x) * (f y * μ y)) = (∑ x, f x * μ x) * (∑ y, f y * μ y) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum]
  rw [h1, h2, h3]; ring


end Lindeberg
end OSSS
end StatMech
