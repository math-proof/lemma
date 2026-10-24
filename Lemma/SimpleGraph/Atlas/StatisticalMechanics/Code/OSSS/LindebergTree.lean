import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.LindebergTree
open Finset StatMech StatMech.OSSS StatMech.OSSS.LindebergTree


/--
[pathPrefix_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma pathPrefix_leaf_eq
  [DecidableEq E]
  {b : Bool}
  {ω : ConfigSpace E}
  {t : ℕ} :
-- imply
  pathPrefix (leaf b) ω t = ∅ := by
-- proof
  apply StatMech.OSSS.LindebergTree.pathPrefix_leaf b ω t

/--
[pathPrefix_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma pathPrefix_zero_eq
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E} :
-- imply
  pathPrefix T ω 0 = ∅ := by
-- proof
  apply StatMech.OSSS.LindebergTree.pathPrefix_zero T ω

/--
[pathPrefix_node_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma pathPrefix_node_succ_eq
  [DecidableEq E]
  {e : E}
  {t f : DecisionTree E}
  {ω : ConfigSpace E}
  {k : ℕ} :
-- imply
  pathPrefix (node e t f) ω (k + 1) = insert e (pathPrefix (if ω e then t else f) ω k) := by
-- proof
  apply StatMech.OSSS.LindebergTree.pathPrefix_node_succ e t f ω k

/--
[queried_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma queried_leaf_eq
  [DecidableEq E]
  {b : Bool}
  {ω : ConfigSpace E} :
-- imply
  (DecisionTree.queried (leaf b) ω) = (∅ : Finset E) := by
-- proof
  apply StatMech.OSSS.LindebergTree.queried_leaf b ω

/--
[queried_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma queried_node_eq
  [DecidableEq E]
  {e : E}
  {l r : DecisionTree E}
  {ω : ConfigSpace E} :
-- imply
  DecisionTree.queried (node e l r) ω = insert e (if ω e then l.queried ω else r.queried ω) := by
-- proof
  apply StatMech.OSSS.LindebergTree.queried_node e l r ω

/--
[pathPrefix_subset_queried](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma pathPrefix_subset_queried_eq
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {t : ℕ} :
-- imply
  pathPrefix T ω t ⊆ T.queried ω := by
-- proof
  apply StatMech.OSSS.LindebergTree.pathPrefix_subset_queried T ω t

/--
[pathPrefix_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma pathPrefix_mono_eq
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {s t : ℕ}
-- given
  (hst : s ≤ t) :
-- imply
  pathPrefix T ω s ⊆ pathPrefix T ω t := by
-- proof
  apply StatMech.OSSS.LindebergTree.pathPrefix_mono T ω hst

/--
[pathPrefix_ge_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma pathPrefix_ge_depth_eq
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {s : ℕ}
-- given
  (hs : treeDepth T ≤ s) :
-- imply
  pathPrefix T ω s = T.queried ω := by
-- proof
  apply StatMech.OSSS.LindebergTree.pathPrefix_ge_depth T ω hs

/--
[pathPrefix_depth_eq_queried](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma pathPrefix_depth_eq_queried_eq
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E} :
-- imply
  pathPrefix T ω (treeDepth T) = T.queried ω := by
-- proof
  apply StatMech.OSSS.LindebergTree.pathPrefix_depth_eq_queried T ω

/--
[adaptM_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma adaptM_zero_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {f : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  adaptM μ T f 0 ω = mean μ f := by
-- proof
  apply StatMech.OSSS.LindebergTree.adaptM_zero hμ1 T f ω

/--
[cExp_queried_evalR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma cExp_queried_evalR_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  cExp μ (T.queried ω) (T.evalR) ω = T.evalR ω := by
-- proof
  apply StatMech.OSSS.LindebergTree.cExp_queried_evalR hpos T ω

/--
[adaptM_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma adaptM_depth_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  adaptM μ T (T.evalR) (treeDepth T) ω = T.evalR ω := by
-- proof
  apply StatMech.OSSS.LindebergTree.adaptM_depth hpos T ω

/--
[evalR_sub_mean_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma evalR_sub_mean_eq_sum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  T.evalR ω - mean μ (T.evalR) = ∑ t ∈ Finset.range (treeDepth T), (adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω) := by
-- proof
  apply StatMech.OSSS.LindebergTree.evalR_sub_mean_eq_sum hpos hμ1 T ω

/--
[meanAbs_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma meanAbs_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  0 ≤ meanAbs μ g := by
-- proof
  apply StatMech.OSSS.LindebergTree.meanAbs_nonneg hpos g

/--
[var_le_meanAbs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma var_le_meanAbs_eq
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
  Lindeberg.var μ f ≤ meanAbs μ (fun ω => f ω - mean μ f) := by
-- proof
  apply StatMech.OSSS.LindebergTree.var_le_meanAbs hpos hμ1 hf0 hf1

/--
[meanAbs_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma meanAbs_sum_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {s : Finset ℕ}
  {g : ℕ → ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  meanAbs μ (fun ω => ∑ t ∈ s, g t ω) ≤ ∑ t ∈ s, meanAbs μ (g t) := by
-- proof
  apply StatMech.OSSS.LindebergTree.meanAbs_sum_le hpos s g

/--
[var_le_sum_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma var_le_sum_step_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  Lindeberg.var μ (T.evalR) ≤ ∑ t ∈ Finset.range (treeDepth T), meanAbs μ (fun ω => adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω) := by
-- proof
  apply StatMech.OSSS.LindebergTree.var_le_sum_step hpos hμ1 T

/--
[freshAt_eq_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma freshAt_eq_diff_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {t : ℕ}
  {e : E} :
-- imply
  freshAt T ω t e = (if e ∈ pathPrefix T ω (t + 1) then (1 : ℝ) else 0) - (if e ∈ pathPrefix T ω t then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.LindebergTree.freshAt_eq_diff T ω t e

/--
[sum_freshAt_eq_queried](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma sum_freshAt_eq_queried_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {e : E} :
-- imply
  ∑ t ∈ Finset.range (treeDepth T), freshAt T ω t e = if e ∈ T.queried ω then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.OSSS.LindebergTree.sum_freshAt_eq_queried T ω e

/--
[pathPrefix_succ_eq_or_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma pathPrefix_succ_eq_or_insert_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {ω : ConfigSpace E}
  {t : ℕ} :
-- imply
  pathPrefix T ω (t + 1) = pathPrefix T ω t ∨ ∃ a, a ∉ pathPrefix T ω t ∧ pathPrefix T ω (t + 1) = insert a (pathPrefix T ω t) := by
-- proof
  apply StatMech.OSSS.LindebergTree.pathPrefix_succ_eq_or_insert T ω t

/--
[adaptM_step_eq_of_prefix_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma adaptM_step_eq_of_prefix_eq_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {ω : ConfigSpace E}
-- given
  (h : pathPrefix T ω (t + 1) = pathPrefix T ω t) :
-- imply
  adaptM μ T f (t + 1) ω = adaptM μ T f t ω := by
-- proof
  apply StatMech.OSSS.LindebergTree.adaptM_step_eq_of_prefix_eq T f t ω h

/--
[abs_step_eq_sum_freshAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma abs_step_eq_sum_freshAt_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {ω : ConfigSpace E} :
-- imply
  |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| = ∑ e, |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e := by
-- proof
  apply StatMech.OSSS.LindebergTree.abs_step_eq_sum_freshAt T f t ω

/--
[sum_step_eq_sum_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma sum_step_eq_sum_edge_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {f : ConfigSpace E → ℝ} :
-- imply
  ∑ t ∈ Finset.range (treeDepth T), meanAbs μ (fun ω => adaptM μ T f (t + 1) ω - adaptM μ T f t ω) = ∑ e, ∑ t ∈ Finset.range (treeDepth T), mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e) := by
-- proof
  apply StatMech.OSSS.LindebergTree.sum_step_eq_sum_edge T f

/--
[revealmentMu_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma revealmentMu_eq_sum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {e : E} :
-- imply
  revealmentMu μ T e = ∑ t ∈ Finset.range (treeDepth T), mean μ (fun ω => freshAt T ω t e) := by
-- proof
  apply StatMech.OSSS.LindebergTree.revealmentMu_eq_sum T e

/--
[mean_freshAt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma mean_freshAt_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  0 ≤ mean μ (fun ω => freshAt T ω t e) := by
-- proof
  apply StatMech.OSSS.LindebergTree.mean_freshAt_nonneg hpos T t e

/--
[cov_coord_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma cov_coord_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f) :
-- imply
  0 ≤ Lindeberg.cov μ f (coord e) := by
-- proof
  apply StatMech.OSSS.LindebergTree.cov_coord_nonneg hpos hμ1 hFKG hf e

/--
[tree_osss](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma tree_osss_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hStep : StepCovBound μ T (T.evalR)) :
-- imply
  Lindeberg.var μ (T.evalR) ≤ ∑ e, revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (coord e) := by
-- proof
  apply StatMech.OSSS.LindebergTree.tree_osss hpos hμ1 T hStep

/--
[tree_osss_revealment_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma tree_osss_revealment_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {D : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hfmono : Monotone (T.evalR))
  (hStep : StepCovBound μ T (T.evalR))
  (hD : ∀ e, revealmentMu μ T e ≤ D) :
-- imply
  Lindeberg.var μ (T.evalR) ≤ D * ∑ e, Lindeberg.cov μ (T.evalR) (coord e) := by
-- proof
  apply StatMech.OSSS.LindebergTree.tree_osss_revealment_le hpos hμ1 hFKG T hfmono hStep D hD

/--
[monotonicOSSSBound_tree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma monotonicOSSSBound_tree_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {D : ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hfmono : Monotone (T.evalR))
  (hStep : StepCovBound μ T (T.evalR))
  (hD : ∀ e, revealmentMu μ T e ≤ D) :
-- imply
  OSSS.MonotonicMeasure.MonotonicOSSSBound μ Finset.univ (T.evalR) 1 1 D := by
-- proof
  apply StatMech.OSSS.LindebergTree.monotonicOSSSBound_tree hpos hμ1 hFKG T hfmono hStep D hD

/--
[fk_tree_osss](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma fk_tree_osss_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {T : DecisionTree (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hStep : StepCovBound (fkMass G p q) T (T.evalR)) :
-- imply
  Lindeberg.var (fkMass G p q) (T.evalR) ≤ ∑ e, revealmentMu (fkMass G p q) T e * Lindeberg.cov (fkMass G p q) (T.evalR) (coord e) := by
-- proof
  apply StatMech.OSSS.LindebergTree.fk_tree_osss G hp hp1 hq T hStep

/--
[fk_monotonicOSSSBound_tree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean)
-/
@[path]
private lemma fk_monotonicOSSSBound_tree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {T : DecisionTree (Sym2 V)}
  {D : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hfmono : Monotone (T.evalR))
  (hStep : StepCovBound (fkMass G p q) T (T.evalR))
  (hD : ∀ e, revealmentMu (fkMass G p q) T e ≤ D) :
-- imply
  OSSS.MonotonicMeasure.MonotonicOSSSBound (fkMass G p q) Finset.univ (T.evalR) 1 1 D := by
-- proof
  apply StatMech.OSSS.LindebergTree.fk_monotonicOSSSBound_tree G hp hp1 hq T hfmono hStep D hD


-- created on 2026-10-23
