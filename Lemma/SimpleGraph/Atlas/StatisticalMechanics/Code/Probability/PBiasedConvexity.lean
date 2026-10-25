import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
open Real Set StatMech StatMech.Probability


/--
[pcx_gpp_bracket_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_gpp_bracket_nonneg_eq
  {p q a c : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (ha : 0 < a)
  (hc : 0 < c)
  (hcon : (1 - p) * a + p * c = 1) :
-- imply
  4 * p * (1 - p) ≤ p * a ^ (q - 2) + (1 - p) * c ^ (q - 2) := by
-- proof
  apply StatMech.Probability.pcx_gpp_bracket_nonneg hp0 hp1 hq1 hq2 ha hc hcon

/--
[pcx_bases_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_bases_pos_eq
  {p : ℝ}
  {x : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hx : x ∈ Set.Ioo (-(1 / (1 - p))) (1 / p)) :
-- imply
  0 < 1 - p * x ∧ 0 < 1 + (1 - p) * x := by
-- proof
  apply StatMech.Probability.pcx_bases_pos hp0 hp1 hx

/--
[pcx_convexOn_g](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_convexOn_g_eq
  {p q : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  ConvexOn ℝ (Set.Icc (-(1 / (1 - p))) (1 / p)) (pcx_g p q) := by
-- proof
  apply StatMech.Probability.pcx_convexOn_g hp0 hp1 hq1 hq2

/--
[pcx_g_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_g_at_zero_eq
  {p q : ℝ} :
-- imply
  pcx_g p q 0 = 0 := by
-- proof
  apply StatMech.Probability.pcx_g_at_zero p q

/--
[pcx_hasDerivAt_g_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_hasDerivAt_g_zero_eq
  {p q : ℝ}
-- given
  (_hp0 : 0 < p)
  (_hp1 : p < 1) :
-- imply
  HasDerivAt (pcx_g p q) 0 0 := by
-- proof
  apply StatMech.Probability.pcx_hasDerivAt_g_zero _hp0 _hp1

/--
[pcx_g_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_g_nonneg_eq
  {p q : ℝ}
  {t : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (ht : t ∈ Set.Icc (-(1 / (1 - p))) (1 / p)) :
-- imply
  0 ≤ pcx_g p q t := by
-- proof
  apply StatMech.Probability.pcx_g_nonneg hp0 hp1 hq1 hq2 ht

/--
[pcx_KEY_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_KEY_pos_eq
  {p q : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  pih_KEY p q := by
-- proof
  apply StatMech.Probability.pcx_KEY_pos hp0 hp1 hq1 hq2

/--
[pcx_KEY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_KEY_eq
  {p q : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  pih_KEY p q := by
-- proof
  apply StatMech.Probability.pcx_KEY hp0 hp1 hq1 hq2

/--
[pcx_OneVarCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_OneVarCore_eq
  {p q : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  pbt_OneVarCore p q := by
-- proof
  apply StatMech.Probability.pcx_OneVarCore hp0 hp1 hq1 hq2

/--
[pcx_two_point_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedConvexity.lean)
-/
@[path]
private lemma pcx_two_point_value_eq
  {p q : ℝ}
  {u v : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  ((1 - p) * u + p * v) ^ 2 + (q - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2 ≤ ((1 - p) * |u| ^ q + p * |v| ^ q) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.pcx_two_point_value hp0 hp1 hq1 hq2 u v


-- created on 2026-10-23
