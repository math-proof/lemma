import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.FullRangeHC
open Finset Real StatMech StatMech.Probability


/--
[frh_lhs_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean)
-/
@[path]
private lemma frh_lhs_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (_hu0 : 0 ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = 4 * (ptn_sigma p) ^ 2 * ∑ e : ι, frh_perCoordWeight p u φ e := by
-- proof
  apply StatMech.Probability.frh_lhs_eq hp0 hp1 φ _hu0 hu1

/--
[frh_perCoordWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean)
-/
@[path]
private lemma frh_perCoordWeight_nonneg_eq
  [Fintype ι]
  [DecidableEq ι]
  {p u : ℝ}
  {φ : ConfigSpace ι → Bool}
  {e : ι} :
-- imply
  0 ≤ frh_perCoordWeight p u φ e := by
-- proof
  apply StatMech.Probability.frh_perCoordWeight_nonneg p u φ e

/--
[frh_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean)
-/
@[path]
private lemma frh_at_zero_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (0:ℝ)) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.frh_at_zero hp0 hp1 φ

/--
[frh_capped_martingale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean)
-/
@[path]
private lemma frh_capped_martingale_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p q' : ℝ}
  {u : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hq1 : 1 ≤ q')
  (hq2 : q' ≤ 2)
  (hu0 : 0 ≤ u)
  (hu1 : u ≤ 1)
  (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p)) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ 4 * (ptn_sigma p) ^ 2 * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.Probability.frh_capped_martingale hp0 hp1 hq1 hq2 hu0 hu1 hrel φ

/--
[frh_capped_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean)
-/
@[path]
private lemma frh_capped_param_eq
  [Fintype ι]
  [DecidableEq ι]
  {p u : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hlo : 1 - 4 * p * (1 - p) ≤ u)
  (hu1 : u ≤ 1) :
-- imply
  ∃ q' : ℝ, 1 ≤ q' ∧ q' ≤ 2 ∧ 1 - u = (q' - 1) * 4 * p * (1 - p) := by
-- proof
  apply StatMech.Probability.frh_capped_param hp0 hp1 hlo hu1

/--
[frh_endpoint_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean)
-/
@[path]
private lemma frh_endpoint_one_eq
  [Fintype ι]
  [DecidableEq ι]
  [Nonempty ι]
  {p : ℝ}
  {φ : ConfigSpace ι → Bool}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (1:ℝ)) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ ((1:ℝ) / (2 - 1)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.frh_endpoint_one hp0 hp1 φ

/--
[frh_martingaleHC_of_openResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean)
-/
@[path]
private lemma frh_martingaleHC_of_openResidue_eq
  [Fintype ι]
  [DecidableEq ι]
  {q : ℝ}
  {H : frh_openResidue q} :
-- imply
  mxd_martingaleHC_statement q := by
-- proof
  apply StatMech.Probability.frh_martingaleHC_of_openResidue H

/--
[frh_lowNoise_range_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean)
-/
@[path]
private lemma frh_lowNoise_range_nonempty_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
-- given
  (hp : 1 / 2 < p)
  (_hp1 : p < 1) :
-- imply
  0 < 1 - 4 * p * (1 - p) := by
-- proof
  apply StatMech.Probability.frh_lowNoise_range_nonempty hp _hp1

/--
[frh_openResidue_c0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean)
-/
@[path]
private lemma frh_openResidue_c0_eq
  [Fintype ι]
  [DecidableEq ι]
  {p : ℝ}
  {E : Type}
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {φ : ConfigSpace E → Bool}
  {u : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  (∑ S : Finset E, (0 : ℝ) * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u)) * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.Probability.frh_openResidue_c0 hp0 hp1 φ u


-- created on 2026-10-23
