import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.StepCov.Part4
open Finset StatMech StatMech.OSSS StatMech.OSSS.StepCov StatMech.OSSS.StepCov.Counterexample


/--
[abs_coord_sub_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma abs_coord_sub_eq_eq
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {ω : ConfigSpace E}
  {N : ℝ}
-- given
  (hN0 : 0 ≤ N)
  (hN1 : N ≤ 1) :
-- imply
  |coord e ω - N| = coord e ω + N - 2 * coord e ω * N := by
-- proof
  apply StatMech.OSSS.StepCov.abs_coord_sub_eq e ω hN0 hN1

/--
[mean_Fmeas_mul_abs_coord_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma mean_Fmeas_mul_abs_coord_sub_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hg : Fmeas F g) :
-- imply
  mean μ (fun ω => g ω * |coord e ω - cExp μ F (coord e) ω|) = 2 * mean μ (fun ω => g ω * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω))) := by
-- proof
  apply StatMech.OSSS.StepCov.mean_Fmeas_mul_abs_coord_sub hpos F e hg

/--
[abs_step_eq_delta_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma abs_step_eq_delta_mul_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {f : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hFKG : FKGLatticeCondition μ)
  (he : e ∉ F)
  (hf : Monotone f)
  (hf0 : 0 ≤ f) :
-- imply
  |cExp μ (insert e F) f ω - cExp μ F f ω| = delta μ F e f ω * |coord e ω - cExp μ F (coord e) ω| := by
-- proof
  apply StatMech.OSSS.StepCov.abs_step_eq_delta_mul hpos hFKG F e he hf hf0 ω

/--
[stepAbs_eq_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma stepAbs_eq_two_mul_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {f : ConfigSpace E → ℝ}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hFKG : FKGLatticeCondition μ)
  (he : e ∉ F)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hg : Fmeas F g) :
-- imply
  mean μ (fun ω => g ω * |cExp μ (insert e F) f ω - cExp μ F f ω|) = 2 * mean μ (fun ω => (g ω * delta μ F e f ω) * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω))) := by
-- proof
  apply StatMech.OSSS.StepCov.stepAbs_eq_two_mul hpos hFKG F e he hf hf0 hg

/--
[pathPrefix_eq_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma pathPrefix_eq_of_agree_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω ω' : ConfigSpace E}
  {t : ℕ}
-- given
  (h : Agree (pathPrefix T ω t) ω ω') :
-- imply
  pathPrefix T ω' t = pathPrefix T ω t := by
-- proof
  apply StatMech.OSSS.StepCov.pathPrefix_eq_of_agree T ω ω' t h

/--
[pathPrefix_succ_eq_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma pathPrefix_succ_eq_of_agree_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω ω' : ConfigSpace E}
  {t : ℕ}
-- given
  (h : Agree (pathPrefix T ω t) ω ω') :
-- imply
  pathPrefix T ω' (t + 1) = pathPrefix T ω (t + 1) := by
-- proof
  apply StatMech.OSSS.StepCov.pathPrefix_succ_eq_of_agree T ω ω' t h

/--
[pathPrefix_eq_Fmeas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma pathPrefix_eq_Fmeas_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {F : Finset E}
  {t : ℕ} :
-- imply
  Fmeas F (fun ω => if pathPrefix T ω t = F then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.StepCov.pathPrefix_eq_Fmeas T F t

/--
[freshPref_Fmeas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma freshPref_Fmeas_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {F : Finset E}
  {e : E}
  {t : ℕ} :
-- imply
  Fmeas F (fun ω => if pathPrefix T ω t = F ∧ pathPrefix T ω (t + 1) = insert e F then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.StepCov.freshPref_Fmeas T F e t

/--
[abs_step_freshAt_eq_sum_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma abs_step_freshAt_eq_sum_prefix_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e = ∑ F ∈ prefSet e, |cExp μ (insert e F) f ω - cExp μ F f ω| * freshPI T ω t e F := by
-- proof
  apply StatMech.OSSS.StepCov.abs_step_freshAt_eq_sum_prefix T f t e ω

/--
[freshPI_Fmeas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma freshPI_Fmeas_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {t : ℕ}
  {e : E}
  {F : Finset E} :
-- imply
  Fmeas F (fun ω => freshPI T ω t e F) := by
-- proof
  apply StatMech.OSSS.StepCov.freshPI_Fmeas T t e F

/--
[freshPI_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma freshPI_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {t : ℕ}
  {e : E}
  {F : Finset E} :
-- imply
  0 ≤ freshPI T ω t e F := by
-- proof
  apply StatMech.OSSS.StepCov.freshPI_nonneg T ω t e F

/--
[mean_step_eq_sum_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma mean_step_eq_sum_prefix_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {e : E} :
-- imply
  mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e) = ∑ F ∈ prefSet e, mean μ (fun ω => |cExp μ (insert e F) f ω - cExp μ F f ω| * freshPI T ω t e F) := by
-- proof
  apply StatMech.OSSS.StepCov.mean_step_eq_sum_prefix T f t e

/--
[mean_step_freshAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma mean_step_freshAt_eq_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f) :
-- imply
  mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e) = 2 * ∑ F ∈ prefSet e, mean μ (fun ω => (freshPI T ω t e F * delta μ F e f ω) * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω))) := by
-- proof
  apply StatMech.OSSS.StepCov.mean_step_freshAt_eq hpos hFKG T hf hf0 t e

/--
[freshAt_eq_sum_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma freshAt_eq_sum_prefix_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {t : ℕ}
  {e : E} :
-- imply
  freshAt T ω t e = ∑ F ∈ prefSet e, freshPI T ω t e F := by
-- proof
  apply StatMech.OSSS.StepCov.freshAt_eq_sum_prefix T ω t e

/--
[mean_freshAt_eq_sum_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma mean_freshAt_eq_sum_prefix_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
  {e : E} :
-- imply
  mean μ (fun ω => freshAt T ω t e) = ∑ F ∈ prefSet e, mean μ (fun ω => freshPI T ω t e F) := by
-- proof
  apply StatMech.OSSS.StepCov.mean_freshAt_eq_sum_prefix T t e

/--
[stepCovBoundTwo_of_cplFKG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma stepCovBoundTwo_of_cplFKG_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hres : ∀ t e, StepCovResidue μ T f t e) :
-- imply
  StepCovBoundTwo μ T f := by
-- proof
  apply StatMech.OSSS.StepCov.stepCovBoundTwo_of_cplFKG hpos hFKG T hf hf0 hres

/--
[var_le_half_meanAbs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma var_le_half_meanAbs_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  Lindeberg.var μ f ≤ (1 / 2) * meanAbs μ (fun ω => f ω - mean μ f) := by
-- proof
  apply StatMech.OSSS.StepCov.var_le_half_meanAbs hpos hμ1 hf0 hf1

/--
[var_le_half_sum_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma var_le_half_sum_step_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  Lindeberg.var μ (T.evalR) ≤ (1 / 2) * ∑ t ∈ Finset.range (treeDepth T), meanAbs μ (fun ω => adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω) := by
-- proof
  apply StatMech.OSSS.StepCov.var_le_half_sum_step hpos hμ1 T

/--
[tree_osss_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma tree_osss_sharp_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hfmono : Monotone (T.evalR))
  (hres : ∀ t e, StepCovResidue μ T (T.evalR) t e) :
-- imply
  Lindeberg.var μ (T.evalR) ≤ ∑ e, revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
-- proof
  apply StatMech.OSSS.StepCov.tree_osss_sharp hpos hμ1 hFKG T hfmono hres

/--
[sum_boolfun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma sum_boolfun_eq
  [Fintype E]
  [DecidableEq E]
  {g : (Bool → Bool) → ℝ} :
-- imply
  (∑ ω : (Bool → Bool), g ω) = g (fun _ => false) + g (fun b => bif b then true else false) + g (fun b => bif b then false else true) + g (fun _ => true) := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.sum_boolfun g

/--
[muU_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma muU_pos_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∀ ω, 0 < muU ω := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.muU_pos

/--
[muU_sum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma muU_sum_one_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∑ ω : ConfigSpace Bool, muU ω = 1 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.muU_sum_one

/--
[mean_fAvg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma mean_fAvg_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  mean muU fAvg = 1 / 2 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.mean_fAvg

/--
[cov_fAvg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma cov_fAvg_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  Lindeberg.cov muU fAvg (coord false) = 1 / 8 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.cov_fAvg

/--
[condNorm_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma condNorm_false_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  condNorm muU {false} (fun _ => false) = 1 / 2 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.condNorm_false

/--
[condNorm_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma condNorm_true_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  condNorm muU {false} (fun _ => true) = 1 / 2 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.condNorm_true

/--
[cExp_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma cExp_false_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  cExp muU {false} fAvg (fun _ => false) = 1 / 4 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.cExp_false

/--
[cExp_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma cExp_true_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  cExp muU {false} fAvg (fun _ => true) = 3 / 4 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.cExp_true

/--
[pathPrefix_Tw_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma pathPrefix_Tw_one_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace Bool} :
-- imply
  pathPrefix Tw ω 1 = {false} := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.pathPrefix_Tw_one ω

/--
[freshAt_Tw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma freshAt_Tw_zero_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace Bool} :
-- imply
  freshAt Tw ω 0 false = 1 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.freshAt_Tw_zero ω

/--
[cExp_false_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma cExp_false_branch_eq
  [Fintype E]
  [DecidableEq E]
  {ω : ConfigSpace Bool} :
-- imply
  cExp muU {false} fAvg ω = if ω false then (3:ℝ)/4 else 1/4 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.cExp_false_branch ω

/--
[mean_step_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma mean_step_witness_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  mean muU (fun ω => |adaptM muU Tw fAvg (0 + 1) ω - adaptM muU Tw fAvg 0 ω| * freshAt Tw ω 0 false) = 1 / 4 := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.mean_step_witness

/--
[stepCovBound_no_factor_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean)
-/
@[path]
private lemma stepCovBound_no_factor_false_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ¬ LindebergTree.StepCovBound muU Tw fAvg := by
-- proof
  apply StatMech.OSSS.StepCov.Counterexample.stepCovBound_no_factor_false


-- created on 2026-10-23
