import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
open StatMech StatMech.Universality


/--
[hexEndpointSAWwt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpointSAWwt_nonneg_eq
  {a : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hexEndpointSAWwt a h0 x ts := by
-- proof
  apply StatMech.Universality.hexEndpointSAWwt_nonneg a h0 hx ts

/--
[hexEndpoint_mem_truncFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_mem_truncFinset_eq
  {a : ℂ}
  {N : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  ts ∈ hexEndpointTruncFinset a h0 N ↔ (ofTurns a h0 ts).EndpointIsLegalSAW ∧ ts.length < N := by
-- proof
  apply StatMech.Universality.hexEndpoint_mem_truncFinset a h0 N ts

/--
[hexEndpoint_levels_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_levels_disjoint_eq
  {a : ℂ}
  {n m : ℕ}
-- given
  (h0 : ℤ)
  (hne : n ≠ m) :
-- imply
  Disjoint (hexEndpointSAWFinset a h0 n) (hexEndpointSAWFinset a h0 m) := by
-- proof
  apply StatMech.Universality.hexEndpoint_levels_disjoint a h0 hne

/--
[hexEndpoint_level_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_level_sum_eq
  {a : ℂ}
  {x : ℝ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  ∑ ts ∈ hexEndpointSAWFinset a h0 n, hexEndpointSAWwt a h0 x ts = hexEndpointCoeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hexEndpoint_level_sum a h0 x n

/--
[hexEndpoint_trunc_sum_eq_coeff_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_trunc_sum_eq_coeff_sum_eq
  {a : ℂ}
  {x : ℝ}
  {N : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  ∑ ts ∈ hexEndpointTruncFinset a h0 N, hexEndpointSAWwt a h0 x ts = ∑ n ∈ Finset.range N, hexEndpointCoeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hexEndpoint_trunc_sum_eq_coeff_sum a h0 x N

/--
[hexEndpoint_finset_sum_le_trunc_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_finset_sum_le_trunc_sum_eq
  {a : ℂ}
  {x : ℝ}
  {s : Finset (List ℤ)}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  ∑ ts ∈ s, hexEndpointSAWwt a h0 x ts ≤ ∑ ts ∈ hexEndpointTruncFinset a h0 (s.sup List.length + 1), hexEndpointSAWwt a h0 x ts := by
-- proof
  apply StatMech.Universality.hexEndpoint_finset_sum_le_trunc_sum a h0 hx s

/--
[hexEndpoint_coeffWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_coeffWeight_nonneg_eq
  {a : ℂ}
  {x : ℝ}
  {n : ℕ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hexEndpointCoeffWeight a h0 x n := by
-- proof
  apply StatMech.Universality.hexEndpoint_coeffWeight_nonneg a h0 hx n

/--
[hexEndpoint_coeff_summable_of_walk_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_coeff_summable_of_walk_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hwalk : Summable (hexEndpointSAWwt a h0 x)) :
-- imply
  Summable (hexEndpointCoeffWeight a h0 x) := by
-- proof
  apply StatMech.Universality.hexEndpoint_coeff_summable_of_walk_summable a h0 hx hwalk

/--
[hexEndpoint_walk_summable_of_coeff_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_walk_summable_of_coeff_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hcoeff : Summable (hexEndpointCoeffWeight a h0 x)) :
-- imply
  Summable (hexEndpointSAWwt a h0 x) := by
-- proof
  apply StatMech.Universality.hexEndpoint_walk_summable_of_coeff_summable a h0 hx hcoeff

/--
[hexEndpoint_walk_summable_iff_coeff_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_walk_summable_iff_coeff_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  Summable (hexEndpointSAWwt a h0 x) ↔ Summable (hexEndpointCoeffWeight a h0 x) := by
-- proof
  apply StatMech.Universality.hexEndpoint_walk_summable_iff_coeff_summable a h0 hx

/--
[hexEndpoint_walk_summable_iff_hlc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_walk_summable_iff_hlc_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 < x) :
-- imply
  Summable (hexEndpointSAWwt a h0 x) ↔ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexEndpoint_walk_summable_iff_hlc a h0 hx

/--
[hexEndpoint_hlc_not_summable_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean)
-/
@[path]
private lemma hexEndpoint_hlc_not_summable_of_walk_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 < x)
  (hdiv : ¬ Summable (hexEndpointSAWwt a h0 x)) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexEndpoint_hlc_not_summable_of_walk a h0 hx hdiv


-- created on 2026-10-23
