import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.BonamiTwoPoint
open Real Set StatMech StatMech.Probability


/--
[bts_convexOn_rpow_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_convexOn_rpow_nonpos_eq
  {c : ℝ}
-- given
  (hc : c ≤ 0) :
-- imply
  ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => x ^ c) := by
-- proof
  apply StatMech.Probability.bts_convexOn_rpow_nonpos hc

/--
[bts_two_le_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_two_le_sum_eq
  {c t : ℝ}
-- given
  (hc : c ≤ 0)
  (ht : |t| < 1) :
-- imply
  (2 : ℝ) ≤ (1 + t) ^ c + (1 - t) ^ c := by
-- proof
  apply StatMech.Probability.bts_two_le_sum hc ht

/--
[bts_convexOn_g](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_convexOn_g_eq
  {q : ℝ}
-- given
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2) :
-- imply
  ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t => (1 + t) ^ q + (1 - t) ^ q - 2 - q * (q - 1) * t ^ 2) := by
-- proof
  apply StatMech.Probability.bts_convexOn_g hq1 hq2

/--
[bts_even_convex_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_even_convex_ge_eq
  {g : ℝ → ℝ}
  {t : ℝ}
-- given
  (hconv : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) g)
  (heven : ∀ t, g (-t) = g t)
  (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
-- imply
  g 0 ≤ g t := by
-- proof
  apply StatMech.Probability.bts_even_convex_ge hconv heven ht

/--
[bts_taylor_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_taylor_lower_eq
  {q t : ℝ}
-- given
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (ht : |t| ≤ 1) :
-- imply
  2 + q * (q - 1) * t ^ 2 ≤ (1 + t) ^ q + (1 - t) ^ q := by
-- proof
  apply StatMech.Probability.bts_taylor_lower hq1 hq2 ht

/--
[bts_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_core_eq
  {q t : ℝ}
-- given
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (ht0 : 0 ≤ t)
  (ht1 : t ≤ 1) :
-- imply
  1 + (q - 1) * t ^ 2 ≤ (((1 + t) ^ q + (1 - t) ^ q) / 2) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.bts_core hq1 hq2 ht0 ht1

/--
[bts_core'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_core'_eq
  {q t : ℝ}
-- given
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (ht0 : 0 ≤ t)
  (ht1 : t ≤ 1) :
-- imply
  t ^ 2 + (q - 1) ≤ (((1 + t) ^ q + (1 - t) ^ q) / 2) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.bts_core' hq1 hq2 ht0 ht1

/--
[bts_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_nonneg_eq
  {q a b : ℝ}
-- given
  (hq1 : 1 ≤ q)
  (hq2 : q ≤ 2)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b) :
-- imply
  a ^ 2 + (q - 1) * b ^ 2 ≤ ((|a + b| ^ q + |a - b| ^ q) / 2) ^ (2 / q) := by
-- proof
  apply StatMech.Probability.bts_nonneg hq1 hq2 ha hb

/--
[bts_abs_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_abs_sum_eq_eq
  {a b q : ℝ} :
-- imply
  abs (|a| + |b|) ^ q + abs (|a| - |b|) ^ q = := by
-- proof
  apply StatMech.Probability.bts_abs_sum_eq a b q

/--
[bts_twoPointScalar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_twoPointScalar_eq
  {ρ : ℝ}
  {a b : ℝ}
-- given
  (h0 : 0 ≤ ρ)
  (h1 : ρ ≤ 1) :
-- imply
  a ^ 2 + ρ ^ 2 * b ^ 2 ≤ ((|a + b| ^ (1 + ρ ^ 2) + |a - b| ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2)) := by
-- proof
  apply StatMech.Probability.bts_twoPointScalar h0 h1 a b

/--
[bts_twoPointScalar_forall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTwoPoint.lean)
-/
@[path]
private lemma bts_twoPointScalar_forall_eq :
-- imply
  ∀ ⦃ρ : ℝ⦄, 0 ≤ ρ → ρ ≤ 1 → ∀ a b : ℝ, a ^ 2 + ρ ^ 2 * b ^ 2 ≤ ((|a + b| ^ (1 + ρ ^ 2) + |a - b| ^ (1 + ρ ^ 2)) / 2) ^ (2 / (1 + ρ ^ 2)) := by
-- proof
  apply StatMech.Probability.bts_twoPointScalar_forall


-- created on 2026-10-23
