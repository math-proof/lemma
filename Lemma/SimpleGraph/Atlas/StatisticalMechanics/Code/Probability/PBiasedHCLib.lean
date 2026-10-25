import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.PBiasedHCLib.Part3
open Real Set StatMech StatMech.Probability


/--
[hclib_jensen_two_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_jensen_two_point_eq
  {r t : ℝ}
-- given
  (hr0 : 0 ≤ r)
  (hr2 : r ≤ 2)
  (ht : |t| ≤ 1) :
-- imply
  ((1 + t) ^ r + (1 - t) ^ r) / 2 ≤ (1 + t ^ 2) ^ (r / 2) := by
-- proof
  apply StatMech.Probability.hclib_jensen_two_point hr0 hr2 ht

/--
[hclib_bracket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_bracket_eq
  {q t : ℝ}
-- given
  (hq2 : 2 ≤ q)
  (hq4 : q ≤ 4)
  (ht : |t| ≤ 1) :
-- imply
  ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2)) / 2 ≤ (1 + (q - 1) * t ^ 2) ^ ((q - 4) / 2) * (1 + (q - 1) ^ 2 * t ^ 2) := by
-- proof
  apply StatMech.Probability.hclib_bracket hq2 hq4 ht

/--
[hclib_BracketResidue_of_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_BracketResidue_of_le_four_eq
  {q : ℝ}
-- given
  (hq2 : 2 ≤ q)
  (hq4 : q ≤ 4) :
-- imply
  hclib_BracketResidue q := by
-- proof
  apply StatMech.Probability.hclib_BracketResidue_of_le_four hq2 hq4

/--
[hclib_w_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_w_pos_eq
  {q t : ℝ}
-- given
  (hq1 : 1 ≤ q) :
-- imply
  0 < 1 + (q - 1) * t ^ 2 := by
-- proof
  apply StatMech.Probability.hclib_w_pos hq1

/--
[hclib_convexOn_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_convexOn_K_eq
  {q : ℝ}
  {Hbr : hclib_BracketResidue q}
-- given
  (hq2 : 2 ≤ q) :
-- imply
  ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (hclib_K q) := by
-- proof
  apply StatMech.Probability.hclib_convexOn_K hq2 Hbr

/--
[hclib_K_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_K_at_zero_eq
  {q : ℝ} :
-- imply
  hclib_K q 0 = 0 := by
-- proof
  apply StatMech.Probability.hclib_K_at_zero q

/--
[hclib_K_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_K_even_eq
  {q t : ℝ} :
-- imply
  hclib_K q (-t) = hclib_K q t := by
-- proof
  apply StatMech.Probability.hclib_K_even q t

/--
[hclib_forward_core_of_bracket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_forward_core_of_bracket_eq
  {q : ℝ}
  {Hbr : hclib_BracketResidue q}
  {t : ℝ}
-- given
  (hq2 : 2 ≤ q)
  (ht : |t| ≤ 1) :
-- imply
  ((1 + t) ^ q + (1 - t) ^ q) / 2 ≤ (1 + (q - 1) * t ^ 2) ^ (q / 2) := by
-- proof
  apply StatMech.Probability.hclib_forward_core_of_bracket hq2 Hbr ht

/--
[hclib_forward_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_forward_core_eq
  {q : ℝ}
  {t : ℝ}
-- given
  (hq2 : 2 ≤ q)
  (hq4 : q ≤ 4)
  (ht : |t| ≤ 1) :
-- imply
  ((1 + t) ^ q + (1 - t) ^ q) / 2 ≤ (1 + (q - 1) * t ^ 2) ^ (q / 2) := by
-- proof
  apply StatMech.Probability.hclib_forward_core hq2 hq4 ht

/--
[hclib_forward_core_2q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_forward_core_2q_eq
  {q : ℝ}
  {t : ℝ}
-- given
  (hq2 : 2 ≤ q)
  (hq4 : q ≤ 4)
  (ht : |t| ≤ 1) :
-- imply
  (((1 + t) ^ q + (1 - t) ^ q) / 2) ^ (2 / q) ≤ 1 + (q - 1) * t ^ 2 := by
-- proof
  apply StatMech.Probability.hclib_forward_core_2q hq2 hq4 ht

/--
[hclib_forward_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_forward_nonneg_eq
  {q a b : ℝ}
-- given
  (hq2 : 2 ≤ q)
  (hq4 : q ≤ 4)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (hab : b ≤ a) :
-- imply
  ((|a + b| ^ q + |a - b| ^ q) / 2) ^ (2 / q) ≤ a ^ 2 + (q - 1) * b ^ 2 := by
-- proof
  apply StatMech.Probability.hclib_forward_nonneg hq2 hq4 ha hb hab

/--
[hclib_two_point_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_two_point_forward_eq
  {q : ℝ}
  {a b : ℝ}
-- given
  (hq2 : 2 ≤ q)
  (hq4 : q ≤ 4) :
-- imply
  ((|a + b| ^ q + |a - b| ^ q) / 2) ^ (2 / q) ≤ a ^ 2 + (q - 1) * b ^ 2 := by
-- proof
  apply StatMech.Probability.hclib_two_point_forward hq2 hq4 a b

/--
[hclib_forward_scalar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_forward_scalar_eq
  {ρ : ℝ}
  {a b : ℝ}
-- given
  (hρ0 : 0 < ρ)
  (hρ1 : ρ ≤ 1)
  (hρlo : (1 : ℝ) / 3 ≤ ρ ^ 2) :
-- imply
  ((|a + ρ * b| ^ (1 + 1 / ρ ^ 2) + |a - ρ * b| ^ (1 + 1 / ρ ^ 2)) / 2) ^ (2 / (1 + 1 / ρ ^ 2)) ≤ a ^ 2 + b ^ 2 := by
-- proof
  apply StatMech.Probability.hclib_forward_scalar hρ0 hρ1 hρlo a b

/--
[hclib_forward_at_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_forward_at_two_eq
  {t : ℝ} :
-- imply
  ((1 + t) ^ (2 : ℝ) + (1 - t) ^ (2 : ℝ)) / 2 = (1 + ((2 : ℝ) - 1) * t ^ 2) ^ ((2 : ℝ) / 2) := by
-- proof
  apply StatMech.Probability.hclib_forward_at_two t

/--
[hclib_forward_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_forward_at_zero_eq
  {q : ℝ} :
-- imply
  ((1 + (0 : ℝ)) ^ q + (1 - (0 : ℝ)) ^ q) / 2 = (1 + (q - 1) * (0 : ℝ) ^ 2) ^ (q / 2) := by
-- proof
  apply StatMech.Probability.hclib_forward_at_zero q

/--
[hclib_reverse_of_bts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_reverse_of_bts_eq
  {t : ℝ}
-- given
  (_ht0 : 0 ≤ t)
  (_ht1 : t ≤ 1) :
-- imply
  (((1 + t) ^ (2 : ℝ) + (1 - t) ^ (2 : ℝ)) / 2) ^ (2 / (2 : ℝ)) = 1 + ((2 : ℝ) - 1) * t ^ 2 := by
-- proof
  apply StatMech.Probability.hclib_reverse_of_bts _ht0 _ht1

/--
[hclib_noncirc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedHCLib.lean)
-/
@[path]
private lemma hclib_noncirc_eq
  {q : ℝ}
  {H : hclib_BracketResidue q}
  {t : ℝ}
-- given
  (ht : |t| ≤ 1) :
-- imply
  ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2)) / 2 ≤ (1 + (q - 1) * t ^ 2) ^ ((q - 4) / 2) * (1 + (q - 1) ^ 2 * t ^ 2) := by
-- proof
  apply StatMech.Probability.hclib_noncirc H t ht


-- created on 2026-10-23
