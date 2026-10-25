/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Def.StatisticalMechanics.Code.OSSS.LindebergTree.Part4
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace LindebergTree

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg

open OSSS.DecisionTree

section Analytic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma meanAbs_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (g : ConfigSpace E → ℝ) :
    0 ≤ meanAbs μ g :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (abs_nonneg _) (hpos ω).le)


lemma var_le_meanAbs {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {f : ConfigSpace E → ℝ} (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f ≤ meanAbs μ (fun ω => f ω - mean μ f) := by
  have hmean0 : 0 ≤ mean μ f := by
    apply Finset.sum_nonneg; intro ω _; exact mul_nonneg (hf0 ω) (hpos ω).le
  have hmean1 : mean μ f ≤ 1 := by
    calc mean μ f = ∑ ω, f ω * μ ω := rfl
      _ ≤ ∑ ω, 1 * μ ω := by
          apply Finset.sum_le_sum; intro ω _
          exact mul_le_mul_of_nonneg_right (hf1 ω) (hpos ω).le
      _ = 1 := by simp_rw [one_mul]; exact hμ1
  
  set m := mean μ f with hm
  have hvareq : Lindeberg.var μ f = ∑ ω, (f ω - m) ^ 2 * μ ω := by
    have hexpand : ∑ ω, (f ω - m) ^ 2 * μ ω
        = (∑ ω, (f ω * f ω) * μ ω) - 2 * m * (∑ ω, f ω * μ ω) + m ^ 2 * (∑ ω, μ ω) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro ω _; ring
    rw [hexpand, hμ1]
    have hms : (∑ ω, f ω * μ ω) = m := rfl
    unfold Lindeberg.var Lindeberg.cov Lindeberg.mean
    rw [show (∑ x, (fun ω => f ω * f ω) x * μ x) = ∑ ω, (f ω * f ω) * μ ω from rfl]
    rw [hms]
    ring
  rw [hvareq]
  unfold meanAbs
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_right _ (hpos ω).le
  
  have hf0ω : (0 : ℝ) ≤ f ω := hf0 ω
  have hf1ω : f ω ≤ 1 := hf1 ω
  have hbound : |f ω - m| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc (f ω - m) ^ 2 = |f ω - m| ^ 2 := by rw [sq_abs]
    _ = |f ω - m| * |f ω - m| := by ring
    _ ≤ |f ω - m| * 1 := mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
    _ = |f ω - m| := by ring


lemma meanAbs_sum_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (s : Finset ℕ)
    (g : ℕ → ConfigSpace E → ℝ) :
    meanAbs μ (fun ω => ∑ t ∈ s, g t ω) ≤ ∑ t ∈ s, meanAbs μ (g t) := by
  unfold meanAbs
  have hswap : (∑ t ∈ s, ∑ ω, |g t ω| * μ ω)
      = ∑ ω, ∑ t ∈ s, |g t ω| * μ ω := Finset.sum_comm
  rw [hswap]
  apply Finset.sum_le_sum
  intro ω _
  simp only []
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (hpos ω).le
  exact Finset.abs_sum_le_sum_abs (fun t => g t ω) s


lemma var_le_sum_step {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) :
    Lindeberg.var μ (T.evalR)
      ≤ ∑ t ∈ Finset.range (treeDepth T),
          meanAbs μ (fun ω => adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω) := by
  have hstep1 := var_le_meanAbs (μ := μ) hpos hμ1
    (f := T.evalR) (fun ω => T.evalR_nonneg ω) (fun ω => T.evalR_le_one ω)
  refine hstep1.trans ?_
  
  have hrw : meanAbs μ (fun ω => T.evalR ω - mean μ (T.evalR))
      = meanAbs μ (fun ω => ∑ t ∈ Finset.range (treeDepth T),
            (adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω)) := by
    unfold meanAbs
    apply Finset.sum_congr rfl
    intro ω _
    simp only []
    rw [evalR_sub_mean_eq_sum hpos hμ1 T ω]
  rw [hrw]
  exact meanAbs_sum_le hpos (Finset.range (treeDepth T))
    (fun t ω => adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω)


end Analytic
end LindebergTree
end OSSS
end StatMech
