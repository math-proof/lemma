import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TreePercolation.Part6
open Set Finset StatMech StatMech.Percolation


/--
[treeGF_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma treeGF_one_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  treeGF b p 1 = 1 := by
-- proof
  apply StatMech.Percolation.treeGF_one b p

/--
[treeGF_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma treeGF_continuous_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  Continuous (treeGF b p) := by
-- proof
  apply StatMech.Percolation.treeGF_continuous b p

/--
[treeGF_eq_pgf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma treeGF_eq_pgf_eq
  {b : ℕ}
  {p s : ℝ} :
-- imply
  treeGF b p s = ∑ k ∈ range (b + 1), binomialOffspringPMF b p k * s ^ k := by
-- proof
  apply StatMech.Percolation.treeGF_eq_pgf b p s

/--
[binomialOffspringPMF_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma binomialOffspringPMF_sum_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  ∑ k ∈ range (b + 1), binomialOffspringPMF b p k = 1 := by
-- proof
  apply StatMech.Percolation.binomialOffspringPMF_sum b p

/--
[treeGF_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma treeGF_hasDerivAt_eq
  {b : ℕ}
  {p s : ℝ} :
-- imply
  HasDerivAt (treeGF b p) ((b : ℝ) * (1 - p + p * s) ^ (b - 1) * p) s := by
-- proof
  apply StatMech.Percolation.treeGF_hasDerivAt b p s

/--
[treeGF_hasDerivAt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma treeGF_hasDerivAt_one_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  HasDerivAt (treeGF b p) ((b : ℝ) * p) 1 := by
-- proof
  apply StatMech.Percolation.treeGF_hasDerivAt_one b p

/--
[treeMean_eq_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma treeMean_eq_deriv_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  treeMean b p = deriv (treeGF b p) 1 := by
-- proof
  apply StatMech.Percolation.treeMean_eq_deriv b p

/--
[one_mem_fixedSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma one_mem_fixedSet_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  (1 : ℝ) ∈ fixedSet b p := by
-- proof
  apply StatMech.Percolation.one_mem_fixedSet b p

/--
[fixedSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma fixedSet_nonempty_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  (fixedSet b p).Nonempty := by
-- proof
  apply StatMech.Percolation.fixedSet_nonempty b p

/--
[fixedSet_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma fixedSet_bddBelow_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  BddBelow (fixedSet b p) := by
-- proof
  apply StatMech.Percolation.fixedSet_bddBelow b p

/--
[fixedSet_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma fixedSet_isClosed_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  IsClosed (fixedSet b p) := by
-- proof
  apply StatMech.Percolation.fixedSet_isClosed b p

/--
[extinctionProb_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma extinctionProb_mem_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  extinctionProb b p ∈ fixedSet b p := by
-- proof
  apply StatMech.Percolation.extinctionProb_mem b p

/--
[extinctionProb_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma extinctionProb_isFixed_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  treeGF b p (extinctionProb b p) = extinctionProb b p := by
-- proof
  apply StatMech.Percolation.extinctionProb_isFixed b p

/--
[extinctionProb_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma extinctionProb_mem_Icc_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  extinctionProb b p ∈ Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Percolation.extinctionProb_mem_Icc b p

/--
[extinctionProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma extinctionProb_nonneg_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  0 ≤ extinctionProb b p := by
-- proof
  apply StatMech.Percolation.extinctionProb_nonneg b p

/--
[extinctionProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma extinctionProb_le_one_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  extinctionProb b p ≤ 1 := by
-- proof
  apply StatMech.Percolation.extinctionProb_le_one b p

/--
[survivalProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma survivalProb_nonneg_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  0 ≤ survivalProb b p := by
-- proof
  apply StatMech.Percolation.survivalProb_nonneg b p

/--
[survivalProb_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma survivalProb_pos_iff_eq
  {b : ℕ}
  {p : ℝ} :
-- imply
  0 < survivalProb b p ↔ extinctionProb b p < 1 := by
-- proof
  apply StatMech.Percolation.survivalProb_pos_iff b p

/--
[treeGF_zero_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma treeGF_zero_nonneg_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hp1 : p ≤ 1) :
-- imply
  0 ≤ treeGF b p 0 := by
-- proof
  apply StatMech.Percolation.treeGF_zero_nonneg b hp1

/--
[supercritical_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma supercritical_fixed_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hp1 : p ≤ 1)
  (hmean : 1 < (b : ℝ) * p) :
-- imply
  ∃ q ∈ Ico (0 : ℝ) 1, treeGF b p q = q := by
-- proof
  apply StatMech.Percolation.supercritical_fixed b hp1 hmean

/--
[subcritical_no_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma subcritical_no_fixed_eq
  {b : ℕ}
  {p s : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hmean : (b : ℝ) * p < 1)
  (hs0 : 0 ≤ s)
  (hs1 : s < 1) :
-- imply
  s < treeGF b p s := by
-- proof
  apply StatMech.Percolation.subcritical_no_fixed b hp0 hp1 hmean hs0 hs1

/--
[survivalProb_eq_zero_of_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma survivalProb_eq_zero_of_subcritical_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hmean : (b : ℝ) * p < 1) :
-- imply
  survivalProb b p = 0 := by
-- proof
  apply StatMech.Percolation.survivalProb_eq_zero_of_subcritical b hp0 hp1 hmean

/--
[survivalProb_pos_of_supercritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma survivalProb_pos_of_supercritical_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hp1 : p ≤ 1)
  (hmean : 1 < (b : ℝ) * p) :
-- imply
  0 < survivalProb b p := by
-- proof
  apply StatMech.Percolation.survivalProb_pos_of_supercritical b hp1 hmean

/--
[survivalProb_zero_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma survivalProb_zero_eq_zero_eq
  {b : ℕ} :
-- imply
  survivalProb b 0 = 0 := by
-- proof
  apply StatMech.Percolation.survivalProb_zero_eq_zero b

/--
[treePc_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma treePc_eq_eq
  {b : ℕ}
-- given
  (hb : 1 ≤ b) :
-- imply
  treePc b = 1 / (b : ℝ) := by
-- proof
  apply StatMech.Percolation.treePc_eq b hb

/--
[survivalProb_pos_of_gt_treePc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma survivalProb_pos_of_gt_treePc_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hb : 1 ≤ b)
  (hp1 : p ≤ 1)
  (hlt : 1 / (b : ℝ) < p) :
-- imply
  0 < survivalProb b p := by
-- proof
  apply StatMech.Percolation.survivalProb_pos_of_gt_treePc b hb hp1 hlt

/--
[survivalProb_eq_zero_of_lt_treePc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean)
-/
@[path]
private lemma survivalProb_eq_zero_of_lt_treePc_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hb : 1 ≤ b)
  (hp0 : 0 ≤ p)
  (hlt : p < 1 / (b : ℝ)) :
-- imply
  survivalProb b p = 0 := by
-- proof
  apply StatMech.Percolation.survivalProb_eq_zero_of_lt_treePc b hb hp0 hlt


-- created on 2026-10-23
