import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.BeffaraDC.ClusterMoments.Part3
open Set Filter Topology StatMech StatMech.BeffaraDC StatMech.BeffaraDC.ClusterSizeDomination


/--
[summable_pow_mul_of_geometricTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma summable_pow_mul_of_geometricTail_eq
  {dist : ℕ → ℝ}
  {C r : ℝ}
  {d : ℕ}
-- given
  (hr0 : 0 ≤ r)
  (hr1 : r < 1)
  (hnn : ∀ n, 0 ≤ dist n)
  (htail : ∀ n, dist n ≤ C * r ^ n) :
-- imply
  Summable (fun n : ℕ => (n : ℝ) ^ d * dist n) := by
-- proof
  apply StatMech.BeffaraDC.summable_pow_mul_of_geometricTail hr0 hr1 hnn htail d

/--
[clusterMoment_summand_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma clusterMoment_summand_summable_eq
  {dist : ℕ → ℝ}
  {C r : ℝ}
  {d : ℕ}
-- given
  (hr0 : 0 ≤ r)
  (hr1 : r < 1)
  (hnn : ∀ n, 0 ≤ dist n)
  (htail : ∀ n, dist n ≤ C * r ^ n) :
-- imply
  Summable (fun n : ℕ => (n : ℝ) ^ d * dist n) := by
-- proof
  apply StatMech.BeffaraDC.clusterMoment_summand_summable hr0 hr1 hnn htail d

/--
[clusterMoment_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma clusterMoment_nonneg_eq
  {dist : ℕ → ℝ}
  {d : ℕ}
-- given
  (hnn : ∀ n, 0 ≤ dist n) :
-- imply
  0 ≤ clusterMoment dist d := by
-- proof
  apply StatMech.BeffaraDC.clusterMoment_nonneg hnn d

/--
[clusterMoment_le_of_geometricTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma clusterMoment_le_of_geometricTail_eq
  {dist : ℕ → ℝ}
  {C r : ℝ}
  {d : ℕ}
-- given
  (hr0 : 0 ≤ r)
  (hr1 : r < 1)
  (hnn : ∀ n, 0 ≤ dist n)
  (htail : ∀ n, dist n ≤ C * r ^ n) :
-- imply
  clusterMoment dist d ≤ ∑' n : ℕ, (n : ℝ) ^ d * (C * r ^ n) := by
-- proof
  apply StatMech.BeffaraDC.clusterMoment_le_of_geometricTail hr0 hr1 hnn htail d

/--
[summand_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma summand_summable_eq
  {D : ClusterSizeDomination}
  {d : ℕ} :
-- imply
  Summable (fun n : ℕ => (n : ℝ) ^ d * D.dist n) := by
-- proof
  apply StatMech.BeffaraDC.ClusterSizeDomination.summand_summable D d

/--
[allMoments_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma allMoments_lt_top_eq
  {D : ClusterSizeDomination}
  {d : ℕ} :
-- imply
  clusterMoment D.dist d ≤ ∑' n : ℕ, (n : ℝ) ^ d * (D.const * D.rate ^ n) := by
-- proof
  apply StatMech.BeffaraDC.ClusterSizeDomination.allMoments_lt_top D d

/--
[moment_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma moment_nonneg_eq
  {D : ClusterSizeDomination}
  {d : ℕ} :
-- imply
  0 ≤ clusterMoment D.dist d := by
-- proof
  apply StatMech.BeffaraDC.ClusterSizeDomination.moment_nonneg D d

/--
[subcritical_expMomentRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma subcritical_expMomentRadius_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hmean : (b : ℝ) * p < 1) :
-- imply
  ∃ s, 1 < s ∧ treeGF b p s < s := by
-- proof
  apply StatMech.BeffaraDC.subcritical_expMomentRadius b hmean

/--
[subcritical_expMomentRadius_of_treeMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma subcritical_expMomentRadius_of_treeMean_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hmean : treeMean b p < 1) :
-- imply
  ∃ s, 1 < s ∧ treeGF b p s < s := by
-- proof
  apply StatMech.BeffaraDC.subcritical_expMomentRadius_of_treeMean b hmean

/--
[subcritical_expectedProgeny](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma subcritical_expectedProgeny_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hmean : (b : ℝ) * p < 1) :
-- imply
  ∑' k : ℕ, ((b : ℝ) * p) ^ k = (1 - (b : ℝ) * p)⁻¹ := by
-- proof
  apply StatMech.BeffaraDC.subcritical_expectedProgeny b hp0 hmean

/--
[subcritical_expectedProgeny_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma subcritical_expectedProgeny_pos_eq
  {b : ℕ}
  {p : ℝ}
-- given
  (hmean : (b : ℝ) * p < 1) :
-- imply
  0 < (1 - (b : ℝ) * p)⁻¹ := by
-- proof
  apply StatMech.BeffaraDC.subcritical_expectedProgeny_pos b hmean

/--
[clusterMoment_lt_top_of_subcriticalDomination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean)
-/
@[path]
private lemma clusterMoment_lt_top_of_subcriticalDomination_eq
  {dist : ℕ → ℝ}
  {C r : ℝ}
  {d : ℕ}
-- given
  (hnn : ∀ n, 0 ≤ dist n)
  (hr0 : 0 ≤ r)
  (hr1 : r < 1)
  (htail : ∀ n, dist n ≤ C * r ^ n) :
-- imply
  clusterMoment dist d ≤ ∑' n : ℕ, (n : ℝ) ^ d * (C * r ^ n) := by
-- proof
  apply StatMech.BeffaraDC.clusterMoment_lt_top_of_subcriticalDomination hnn hr0 hr1 htail d


-- created on 2026-10-23
