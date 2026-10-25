/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Def.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
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


lemma sum_step_eq_sum_edge {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) :
    ∑ t ∈ Finset.range (treeDepth T),
        meanAbs μ (fun ω => adaptM μ T f (t + 1) ω - adaptM μ T f t ω)
      = ∑ e, ∑ t ∈ Finset.range (treeDepth T),
          mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  
  unfold meanAbs mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [abs_step_eq_sum_freshAt T f t ω, Finset.sum_mul]


lemma revealmentMu_eq_sum {μ : ConfigSpace E → ℝ} (T : DecisionTree E) (e : E) :
    revealmentMu μ T e
      = ∑ t ∈ Finset.range (treeDepth T), mean μ (fun ω => freshAt T ω t e) := by
  unfold revealmentMu mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.sum_mul, sum_freshAt_eq_queried T ω e]


lemma mean_freshAt_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) (e : E) :
    0 ≤ mean μ (fun ω => freshAt T ω t e) := by
  unfold mean
  apply Finset.sum_nonneg; intro ω _
  refine mul_nonneg ?_ (hpos ω).le
  show 0 ≤ freshAt T ω t e
  unfold freshAt; split <;> norm_num


lemma cov_coord_nonneg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) {f : ConfigSpace E → ℝ} (hf : Monotone f) (e : E) :
    0 ≤ Lindeberg.cov μ f (coord e) := by
  have hfkg := mean_mul_ge hpos hμ1 hFKG hf (coord_mono e)
  unfold Lindeberg.cov
  linarith [hfkg]


theorem tree_osss {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) (hStep : StepCovBound μ T (T.evalR)) :
    Lindeberg.var μ (T.evalR)
      ≤ ∑ e, revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
  
  have h1 := var_le_sum_step hpos hμ1 T
  rw [sum_step_eq_sum_edge T (T.evalR)] at h1
  refine h1.trans ?_
  
  apply Finset.sum_le_sum
  intro e _
  
  calc ∑ t ∈ Finset.range (treeDepth T),
        mean μ (fun ω => |adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω| * freshAt T ω t e)
      ≤ ∑ t ∈ Finset.range (treeDepth T),
          Lindeberg.cov μ (T.evalR) (coord e) * mean μ (fun ω => freshAt T ω t e) :=
        Finset.sum_le_sum (fun t _ => hStep t e)
    _ = Lindeberg.cov μ (T.evalR) (coord e) * ∑ t ∈ Finset.range (treeDepth T),
          mean μ (fun ω => freshAt T ω t e) := by rw [← Finset.mul_sum]
    _ = revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
        rw [revealmentMu_eq_sum]; ring


theorem tree_osss_revealment_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    (hfmono : Monotone (T.evalR)) (hStep : StepCovBound μ T (T.evalR))
    (D : ℝ) (hD : ∀ e, revealmentMu μ T e ≤ D) :
    Lindeberg.var μ (T.evalR) ≤ D * ∑ e, Lindeberg.cov μ (T.evalR) (coord e) := by
  refine (tree_osss hpos hμ1 T hStep).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hcov : 0 ≤ Lindeberg.cov μ (T.evalR) (coord e) :=
    cov_coord_nonneg hpos hμ1 hFKG hfmono e
  exact mul_le_mul_of_nonneg_right (hD e) hcov


theorem monotonicOSSSBound_tree {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    (hfmono : Monotone (T.evalR)) (hStep : StepCovBound μ T (T.evalR))
    (D : ℝ) (hD : ∀ e, revealmentMu μ T e ≤ D) :
    OSSS.MonotonicMeasure.MonotonicOSSSBound μ Finset.univ (T.evalR) 1 1 D := by
  unfold OSSS.MonotonicMeasure.MonotonicOSSSBound
  rw [← Lindeberg.var_eq_genVar, Nat.cast_one, one_mul, one_mul]
  have hmain := tree_osss_revealment_le hpos hμ1 hFKG T hfmono hStep D hD
  refine hmain.trans (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  
  rw [← Lindeberg.cov_eq_genCov, ← Lindeberg.coord_eq_genCoord]
  unfold Lindeberg.cov Lindeberg.mean
  rw [show (fun ω => T.evalR ω * coord e ω) = (fun ω => coord e ω * T.evalR ω) from by
        funext ω; ring]
  ring

end Analytic


section FK

open MonotonicFK OSSS.MonotonicMeasure


theorem fk_tree_osss {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (T : DecisionTree (Sym2 V))
    (hStep : StepCovBound (fkMass G p q) T (T.evalR)) :
    Lindeberg.var (fkMass G p q) (T.evalR)
      ≤ ∑ e, revealmentMu (fkMass G p q) T e
          * Lindeberg.cov (fkMass G p q) (T.evalR) (coord e) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact tree_osss (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0) T hStep


theorem fk_monotonicOSSSBound_tree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (T : DecisionTree (Sym2 V))
    (hfmono : Monotone (T.evalR)) (hStep : StepCovBound (fkMass G p q) T (T.evalR))
    (D : ℝ) (hD : ∀ e, revealmentMu (fkMass G p q) T e ≤ D) :
    OSSS.MonotonicMeasure.MonotonicOSSSBound (fkMass G p q) Finset.univ (T.evalR) 1 1 D := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact monotonicOSSSBound_tree (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0)
    (FK.fkProb_FKGLatticeCondition G hp hp1 hq) T hfmono hStep D hD

end FK
end LindebergTree
end OSSS
end StatMech
