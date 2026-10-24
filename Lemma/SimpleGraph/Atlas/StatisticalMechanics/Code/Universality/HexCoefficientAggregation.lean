import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexCoefficientAggregation
open StatMech StatMech.Universality


/--
[hzc_coeffWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_coeffWeight_nonneg_eq
  {a : ℂ}
  {x : ℝ}
  {n : ℕ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hzc_coeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hzc_coeffWeight_nonneg a h0 hx n

/--
[hzc_coeffWeight_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_coeffWeight_zero_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  hzc_coeffWeight a h0 x 0 = 0 := by
-- proof
  apply StatMech.Universality.hzc_coeffWeight_zero a h0 x

/--
[hzc_hexSAWwt_zero_fugacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_hexSAWwt_zero_fugacity_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  hexSAWwt a h0 0 ts = 0 := by
-- proof
  apply StatMech.Universality.hzc_hexSAWwt_zero_fugacity a h0 ts

/--
[hzc_coeffWeight_zero_fugacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_coeffWeight_zero_fugacity_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hzc_coeffWeight a h0 0 n = 0 := by
-- proof
  apply StatMech.Universality.hzc_coeffWeight_zero_fugacity a h0 n

/--
[hzc_truncFinset_eq_empty_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_truncFinset_eq_empty_of_le_one_eq
  {a : ℂ}
  {N : ℕ}
-- given
  (h0 : ℤ)
  (hN : N ≤ 1) :
-- imply
  hzc_truncFinset a h0 N = ∅ := by
-- proof
  apply StatMech.Universality.hzc_truncFinset_eq_empty_of_le_one a h0 hN

/--
[hzc_truncFinset_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_truncFinset_zero_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hzc_truncFinset a h0 0 = ∅ := by
-- proof
  apply StatMech.Universality.hzc_truncFinset_zero a h0

/--
[hzc_truncFinset_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_truncFinset_one_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hzc_truncFinset a h0 1 = ∅ := by
-- proof
  apply StatMech.Universality.hzc_truncFinset_one a h0

/--
[hzc_trunc_sum_eq_coeff_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_trunc_sum_eq_coeff_sum_eq
  {a : ℂ}
  {x : ℝ}
  {N : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts = ∑ n ∈ Finset.range N, hzc_coeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hzc_trunc_sum_eq_coeff_sum a h0 x N

/--
[hzc_finset_sum_le_trunc_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_finset_sum_le_trunc_sum_eq
  {a : ℂ}
  {x : ℝ}
  {s : Finset (List ℤ)}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  ∑ ts ∈ s, hexSAWwt a h0 x ts ≤ ∑ ts ∈ hzc_truncFinset a h0 (s.sup (fun ts => (ofTurns a h0 ts).numVertices) + 1), hexSAWwt a h0 x ts := by
-- proof
  apply StatMech.Universality.hzc_finset_sum_le_trunc_sum a h0 hx s

/--
[hzc_coeff_summable_of_walk_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_coeff_summable_of_walk_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hwalk : Summable (hexSAWwt a h0 x)) :
-- imply
  Summable (hzc_coeffWeight a h0 x) := by
-- proof
  apply StatMech.Universality.hzc_coeff_summable_of_walk_summable a h0 hx hwalk

/--
[hzc_walk_summable_of_coeff_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_walk_summable_of_coeff_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hcoeff : Summable (hzc_coeffWeight a h0 x)) :
-- imply
  Summable (hexSAWwt a h0 x) := by
-- proof
  apply StatMech.Universality.hzc_walk_summable_of_coeff_summable a h0 hx hcoeff

/--
[hzc_walk_summable_iff_coeff_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_walk_summable_iff_coeff_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  Summable (hexSAWwt a h0 x) ↔ Summable (hzc_coeffWeight a h0 x) := by
-- proof
  apply StatMech.Universality.hzc_walk_summable_iff_coeff_summable a h0 hx

/--
[hzc_tsum_eq_coeff_tsum_of_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_tsum_eq_coeff_tsum_of_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hwalk : Summable (hexSAWwt a h0 x)) :
-- imply
  (∑' ts, hexSAWwt a h0 x ts) = ∑' n, hzc_coeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hzc_tsum_eq_coeff_tsum_of_summable a h0 hx hwalk

/--
[hzc_tsum_eq_coeff_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_tsum_eq_coeff_tsum_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  (∑' ts, hexSAWwt a h0 x ts) = ∑' n, hzc_coeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hzc_tsum_eq_coeff_tsum a h0 hx

/--
[hzc_trunc_sum_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_trunc_sum_tendsto_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hwalk : Summable (hexSAWwt a h0 x)) :
-- imply
  Filter.Tendsto (fun N => ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts) Filter.atTop (nhds (∑' ts, hexSAWwt a h0 x ts)) := by
-- proof
  apply StatMech.Universality.hzc_trunc_sum_tendsto a h0 hx hwalk

/--
[hzc_walk_hasSum_iff_coeff_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_walk_hasSum_iff_coeff_hasSum_eq
  {a : ℂ}
  {x : ℝ}
  {z : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  HasSum (hexSAWwt a h0 x) z ↔ HasSum (hzc_coeffWeight a h0 x) z := by
-- proof
  apply StatMech.Universality.hzc_walk_hasSum_iff_coeff_hasSum a h0 hx z

/--
[hzc_summable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_summable_iff_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) ↔ Summable (fun n : ℕ => (hzc_sawCount a h0 n : ℝ) * x ^ n) := by
-- proof
  apply StatMech.Universality.hzc_summable_iff a h0 hx

/--
[hzc_tsum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_tsum_eq_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  (∑' ts : List ℤ, hexSAWwt a h0 x ts) = ∑' n : ℕ, (hzc_sawCount a h0 n : ℝ) * x ^ n := by
-- proof
  apply StatMech.Universality.hzc_tsum_eq a h0 hx

/--
[hzc_hasSum_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_hasSum_iff_eq
  {a : ℂ}
  {x : ℝ}
  {z : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  HasSum (fun ts : List ℤ => hexSAWwt a h0 x ts) z ↔ HasSum (fun n : ℕ => (hzc_sawCount a h0 n : ℝ) * x ^ n) z := by
-- proof
  apply StatMech.Universality.hzc_hasSum_iff a h0 hx z

/--
[hlc_coeffWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hlc_coeffWeight_nonneg_eq
  {a : ℂ}
  {x : ℝ}
  {n : ℕ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hlc_coeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hlc_coeffWeight_nonneg a h0 hx n

/--
[hlc_coeffWeight_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hlc_coeffWeight_zero_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  hlc_coeffWeight a h0 x 0 = 1 := by
-- proof
  apply StatMech.Universality.hlc_coeffWeight_zero a h0 x

/--
[hlc_coeffWeight_zero_fugacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hlc_coeffWeight_zero_fugacity_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hlc_coeffWeight a h0 0 n = if n = 0 then 1 else 0 := by
-- proof
  apply StatMech.Universality.hlc_coeffWeight_zero_fugacity a h0 n

/--
[hzc_coeffWeight_succ_eq_mul_hlc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_coeffWeight_succ_eq_mul_hlc_eq
  {a : ℂ}
  {x : ℝ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hzc_coeffWeight a h0 x (n + 1) = x * hlc_coeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hzc_coeffWeight_succ_eq_mul_hlc a h0 x n

/--
[hzc_coeff_sum_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_coeff_sum_shift_eq
  {a : ℂ}
  {x : ℝ}
  {N : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  ∑ k ∈ Finset.range (N + 1), hzc_coeffWeight a h0 x k = x * ∑ n ∈ Finset.range N, hlc_coeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hzc_coeff_sum_shift a h0 x N

/--
[hlc_trunc_sum_eq_mul_coeff_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hlc_trunc_sum_eq_mul_coeff_sum_eq
  {a : ℂ}
  {x : ℝ}
  {N : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  ∑ ts ∈ hzc_truncFinset a h0 (N + 1), hexSAWwt a h0 x ts = x * ∑ n ∈ Finset.range N, hlc_coeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hlc_trunc_sum_eq_mul_coeff_sum a h0 x N

/--
[hzc_coeff_summable_iff_hlc_coeff_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_coeff_summable_iff_hlc_coeff_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  Summable (hzc_coeffWeight a h0 x) ↔ Summable (hlc_coeffWeight a h0 x) := by
-- proof
  apply StatMech.Universality.hzc_coeff_summable_iff_hlc_coeff_summable a h0 hx

/--
[hlc_summable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hlc_summable_iff_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) ↔ Summable (fun n : ℕ => (hlc_sawCount a h0 n : ℝ) * x ^ n) := by
-- proof
  apply StatMech.Universality.hlc_summable_iff a h0 hx

/--
[hzc_coeff_tsum_eq_mul_hlc_coeff_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hzc_coeff_tsum_eq_mul_hlc_coeff_tsum_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  (∑' n, hzc_coeffWeight a h0 x n) = x * ∑' n, hlc_coeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hzc_coeff_tsum_eq_mul_hlc_coeff_tsum a h0 hx

/--
[hlc_tsum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hlc_tsum_eq_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  (∑' ts : List ℤ, hexSAWwt a h0 x ts) = x * ∑' n : ℕ, (hlc_sawCount a h0 n : ℝ) * x ^ n := by
-- proof
  apply StatMech.Universality.hlc_tsum_eq a h0 hx

/--
[hlc_walk_hasSum_of_coeff_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCoefficientAggregation.lean)
-/
@[path]
private lemma hlc_walk_hasSum_of_coeff_hasSum_eq
  {a : ℂ}
  {x z : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hcoeff : HasSum (fun n : ℕ => (hlc_sawCount a h0 n : ℝ) * x ^ n) z) :
-- imply
  HasSum (fun ts : List ℤ => hexSAWwt a h0 x ts) (x * z) := by
-- proof
  apply StatMech.Universality.hlc_walk_hasSum_of_coeff_hasSum a h0 hx hcoeff


-- created on 2026-10-23
