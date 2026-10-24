import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.PBiasedIntegralHC
open Real Set StatMech StatMech.Probability


/--
[pih_g_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_g_eq_eq
  {p q z : ℝ} :
-- imply
  pbt_g p q z = (pih_m p z) ^ 2 + pih_V p q z := by
-- proof
  apply StatMech.Probability.pih_g_eq p q z

/--
[pih_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_bernoulli_eq
  {p q z : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hz : 0 ≤ z) :
-- imply
  (pbt_g p q z) ^ (q / 2) ≤ (pih_m p z) ^ q + (q / 2) * (pih_m p z) ^ (q - 2) * pih_V p q z := by
-- proof
  apply StatMech.Probability.pih_bernoulli hp0 hp1 hq1 hq2 hz

/--
[pih_core_of_KEY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_core_of_KEY_eq
  {p q : ℝ}
  {HKEY : pih_KEY p q}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  pbt_OneVarCore p q := by
-- proof
  apply StatMech.Probability.pih_core_of_KEY hp0 hp1 hq1 hq2 HKEY

/--
[pih_KEY_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_KEY_half_eq
  {q : ℝ}
-- given
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  pih_KEY (1 / 2) q := by
-- proof
  apply StatMech.Probability.pih_KEY_half hq1 hq2

/--
[pih_KEY_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_KEY_at_one_eq
  {p q : ℝ} :
-- imply
  (q / 2) * (pih_m p 1) ^ (q - 2) * pih_V p q 1 ≤ (1 - p) + p * (1 : ℝ) ^ q - (pih_m p 1) ^ q := by
-- proof
  apply StatMech.Probability.pih_KEY_at_one p q

/--
[pih_KEY_q_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_KEY_q_one_eq
  {p : ℝ} :
-- imply
  pih_KEY p 1 := by
-- proof
  apply StatMech.Probability.pih_KEY_q_one p

/--
[pih_slack_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_slack_nonneg_eq
  {p q z : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1)
  (hq1 : 1 ≤ q)
  (hz : 0 ≤ z) :
-- imply
  0 ≤ (1 - p) + p * z ^ q - (pih_m p z) ^ q := by
-- proof
  apply StatMech.Probability.pih_slack_nonneg hp0 hp1 hq1 hz

/--
[pih_slack_crux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_slack_crux_eq
  {p q z : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (hz : 0 < z) :
-- imply
  p * (pih_m p z) ^ (q - 2) ≤ z ^ (q - 2) := by
-- proof
  apply StatMech.Probability.pih_slack_crux hp0 hp1 hq1 hq2 hz

/--
[pih_KEY_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_KEY_satisfiable_eq :
-- imply
  (∀ p, pih_KEY p 1) ∧ (∀ q, 1 ≤ q → q ≤ 2 → pih_KEY (1 / 2) q) := by
-- proof
  apply StatMech.Probability.pih_KEY_satisfiable

/--
[pih_KEY_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_KEY_noncirc_eq
  {p q : ℝ}
  {H : pih_KEY p q}
  {z : ℝ}
-- given
  (hz : 0 ≤ z) :
-- imply
  (q / 2) * ((1 - p) + p * z) ^ (q - 2) * (4 * (q - 1) * p ^ 2 * (1 - p) ^ 2 * (z - 1) ^ 2) ≤ (1 - p) + p * z ^ q - ((1 - p) + p * z) ^ q := by
-- proof
  apply StatMech.Probability.pih_KEY_noncirc H z hz

/--
[pih_two_point_value_of_KEY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean)
-/
@[path]
private lemma pih_two_point_value_of_KEY_eq
  {p q : ℝ}
  {HKEY : pih_KEY p q}
  {HKEY' : pih_KEY (1 - p) q}
  {u v : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2 ≤ ((1 - p) * |u| ^ q + p * |v| ^ q) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.pih_two_point_value_of_KEY hp0 hp1 hq1 hq2 HKEY HKEY' u v


-- created on 2026-10-23
