/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
import Def.StatisticalMechanics.Code.OSSS.StepCov.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace StepCov

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg OSSS.LindebergTree

open OSSS.DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem stepCovBoundTwo_of_cplFKG {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hres : ∀ t e, StepCovResidue μ T f t e) :
    StepCovBoundTwo μ T f := by
  intro t e
  rw [mean_step_freshAt_eq hpos hFKG T hf hf0 t e, mean_freshAt_eq_sum_prefix T t e]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  calc ∑ F ∈ prefSet e,
        mean μ (fun ω => (freshPI T ω t e F * delta μ F e f ω)
            * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω)))
      ≤ ∑ F ∈ prefSet e, Lindeberg.cov μ f (coord e) * mean μ (fun ω => freshPI T ω t e F) :=
        Finset.sum_le_sum (fun F hF => hres t e F hF)
    _ = Lindeberg.cov μ f (coord e) * ∑ F ∈ prefSet e, mean μ (fun ω => freshPI T ω t e F) := by
        rw [Finset.mul_sum]


theorem var_le_half_meanAbs {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {f : ConfigSpace E → ℝ} (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f ≤ (1 / 2) * meanAbs μ (fun ω => f ω - mean μ f) := by
  have hmean0 : 0 ≤ mean μ f :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (hf0 ω) (hpos ω).le)
  have hmean1 : mean μ f ≤ 1 := by
    calc mean μ f = ∑ ω, f ω * μ ω := rfl
      _ ≤ ∑ ω, 1 * μ ω := Finset.sum_le_sum (fun ω _ =>
            mul_le_mul_of_nonneg_right (hf1 ω) (hpos ω).le)
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
    rw [show (∑ x, (fun ω => f ω * f ω) x * μ x) = ∑ ω, (f ω * f ω) * μ ω from rfl, hms]; ring
  rw [hvareq]
  
  have hbal : ∑ ω, (f ω - m) * μ ω = 0 := by
    rw [show (fun ω => (f ω - m) * μ ω) = (fun ω => f ω * μ ω - m * μ ω) from by funext ω; ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hμ1, mul_one]
    have : (∑ ω, f ω * μ ω) = m := rfl
    rw [this]; ring
  
  
  
  have hkey : ∀ ω, (f ω - m) ^ 2 * μ ω
      ≤ (1 / 2) * (|f ω - m| * μ ω) + (1 / 2) * ((f ω - m) * (1 - 2 * m) * μ ω) := by
    intro ω
    have hμω := (hpos ω).le
    have hf0ω : (0:ℝ) ≤ f ω := hf0 ω
    have hf1ω : f ω ≤ 1 := hf1 ω
    
    have hpt : (f ω - m) ^ 2 ≤ (1 / 2) * |f ω - m| + (1 / 2) * ((f ω - m) * (1 - 2 * m)) := by
      by_cases hsign : m ≤ f ω
      · rw [abs_of_nonneg (by linarith)]
        nlinarith [sq_nonneg (f ω - m), mul_nonneg (sub_nonneg.mpr hsign) (sub_nonneg.mpr hf1ω)]
      · replace hsign : f ω < m := lt_of_not_ge hsign
        rw [abs_of_neg (by linarith)]
        nlinarith [sq_nonneg (f ω - m), mul_nonneg (le_of_lt (sub_pos.mpr hsign)) hmean0]
    calc (f ω - m) ^ 2 * μ ω
        ≤ ((1 / 2) * |f ω - m| + (1 / 2) * ((f ω - m) * (1 - 2 * m))) * μ ω :=
          mul_le_mul_of_nonneg_right hpt hμω
      _ = (1 / 2) * (|f ω - m| * μ ω) + (1 / 2) * ((f ω - m) * (1 - 2 * m) * μ ω) := by ring
  calc ∑ ω, (f ω - m) ^ 2 * μ ω
      ≤ ∑ ω, ((1 / 2) * (|f ω - m| * μ ω) + (1 / 2) * ((f ω - m) * (1 - 2 * m) * μ ω)) :=
        Finset.sum_le_sum (fun ω _ => hkey ω)
    _ = (1 / 2) * (∑ ω, |f ω - m| * μ ω)
          + (1 / 2) * (1 - 2 * m) * (∑ ω, (f ω - m) * μ ω) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [show (∑ ω, (f ω - m) * (1 - 2 * m) * μ ω)
              = (1 - 2 * m) * ∑ ω, (f ω - m) * μ ω from by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)]
        ring
    _ = (1 / 2) * meanAbs μ (fun ω => f ω - m) := by
        rw [hbal, mul_zero, add_zero]; unfold meanAbs; rfl


lemma var_le_half_sum_step {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) :
    Lindeberg.var μ (T.evalR)
      ≤ (1 / 2) * ∑ t ∈ Finset.range (treeDepth T),
          meanAbs μ (fun ω => adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω) := by
  have hstep1 := var_le_half_meanAbs (μ := μ) hpos hμ1
    (f := T.evalR) (fun ω => T.evalR_nonneg ω) (fun ω => T.evalR_le_one ω)
  refine hstep1.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1 / 2)
  
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


theorem tree_osss_sharp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) (T : DecisionTree E) (hfmono : Monotone (T.evalR))
    (hres : ∀ t e, StepCovResidue μ T (T.evalR) t e) :
    Lindeberg.var μ (T.evalR)
      ≤ ∑ e, revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
  have hStep : StepCovBoundTwo μ T (T.evalR) :=
    stepCovBoundTwo_of_cplFKG hpos hFKG T hfmono (fun ω => T.evalR_nonneg ω) hres
  
  have h1 := var_le_half_sum_step hpos hμ1 T
  rw [sum_step_eq_sum_edge T (T.evalR)] at h1
  refine h1.trans ?_
  
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  
  calc (1 / 2) * ∑ t ∈ Finset.range (treeDepth T),
        mean μ (fun ω => |adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω| * freshAt T ω t e)
      ≤ (1 / 2) * ∑ t ∈ Finset.range (treeDepth T),
          2 * (Lindeberg.cov μ (T.evalR) (coord e) * mean μ (fun ω => freshAt T ω t e)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1 / 2)
        exact Finset.sum_le_sum (fun t _ => hStep t e)
    _ = Lindeberg.cov μ (T.evalR) (coord e) * ∑ t ∈ Finset.range (treeDepth T),
          mean μ (fun ω => freshAt T ω t e) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
    _ = revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
        rw [revealmentMu_eq_sum]; ring


namespace Counterexample


lemma sum_boolfun (g : (Bool → Bool) → ℝ) :
    (∑ ω : (Bool → Bool), g ω) =
      g (fun _ => false) + g (fun b => bif b then true else false)
        + g (fun b => bif b then false else true) + g (fun _ => true) := by
  rw [show (Finset.univ : Finset (Bool → Bool))
        = {(fun _ => false), (fun b => bif b then true else false),
            (fun b => bif b then false else true), (fun _ => true)} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring


end Counterexample
end StepCov
end OSSS
end StatMech
