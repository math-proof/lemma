import Mathlib
import sympy.Basic
import sympy.series.formal.LimitsDetails
open PowerSeries
open Seq
open scoped PowerSeries BigOperators Polynomial


/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma stabilizes_to_unique_prime_eq
-- given
  {a : ℕ → K}
  {limit1 limit2 : K}
  (ha : StabilizesTo a limit1)
  (hb : StabilizesTo a limit2) :
-- imply
  limit1 = limit2 := by
-- proof
  apply Seq.stabilizesTo_unique' ha hb

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma exists_xn_equiv_k_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {lf : PowerSeries K}
  (hf : CoeffStabilizesTo f lf)
  (n : ℕ) :
-- imply
  ∃ K : ℕ, ∀ i ≥ K, XnEquiv n (f i) lf := by
-- proof
  apply PowerSeries.exists_xnEquiv_K hf n

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma exists_xn_equiv_l_is
  [CommRing K]
-- given
  {g : ℕ → PowerSeries K}
  {lg : PowerSeries K}
  (hg : CoeffStabilizesTo g lg)
  (n : ℕ) :
-- imply
  ∃ L : ℕ, ∀ i ≥ L, XnEquiv n (g i) lg := by
-- proof
  apply PowerSeries.exists_xnEquiv_L hg n

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma exists_xn_equiv_both_is
  [CommRing K]
-- given
  {f g : ℕ → PowerSeries K}
  {lf lg : PowerSeries K}
  (hf : CoeffStabilizesTo f lf)
  (hg : CoeffStabilizesTo g lg)
  (n : ℕ) :
-- imply
  ∃ P : ℕ, ∀ i ≥ P, XnEquiv n (f i) lf ∧ XnEquiv n (g i) lg := by
-- proof
  apply PowerSeries.exists_xnEquiv_both hf hg n

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_add_prime_is
  [CommRing K]
-- given
  {f g : ℕ → PowerSeries K}
  {lf lg : PowerSeries K}
  (hf : CoeffStabilizesTo f lf)
  (hg : CoeffStabilizesTo g lg) :
-- imply
  CoeffStabilizesTo (fun i => f i + g i) (lf + lg) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_add' hf hg

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_mul_prime_is
  [CommRing K]
-- given
  {f g : ℕ → PowerSeries K}
  {lf lg : PowerSeries K}
  (hf : CoeffStabilizesTo f lf)
  (hg : CoeffStabilizesTo g lg) :
-- imply
  CoeffStabilizesTo (fun i => f i * g i) (lf * lg) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_mul' hf hg

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_partial_sum_prime_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hf : IsSummable f) :
-- imply
  CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) (tsum' f hf) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_partial_sum' hf

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma coeff_stabilizes_to_partial_prod_prime_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hf : IsMultipliable f) :
-- imply
  CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) (tprod' f hf) := by
-- proof
  apply PowerSeries.coeffStabilizesTo_partial_prod' hf

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma is_summable_of_coeff_stabilizes_to_partial_sum_prime_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  {limit : PowerSeries K}
  (h : CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) limit) :
-- imply
  IsSummable f := by
-- proof
  apply PowerSeries.isSummable_of_coeffStabilizesTo_partial_sum' h

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma tsum_prime_eq_of_coeff_stabilizes_to_partial_sum_prime_eq
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hsum : IsSummable f)
  {limit : PowerSeries K}
  (h : CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) limit) :
-- imply
  tsum' f hsum = limit := by
-- proof
  apply PowerSeries.tsum'_eq_of_coeffStabilizesTo_partial_sum' h hsum

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma is_multipliable_of_coeff_stabilizes_to_partial_prod_prime_is
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hconst : ∀ i, constantCoeff (f i) = 1)
  {limit : PowerSeries K}
  (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) limit) :
-- imply
  IsMultipliable f := by
-- proof
  apply PowerSeries.isMultipliable_of_coeffStabilizesTo_partial_prod' h hconst

/--
[LimitsDetails](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/Limits.lean)
-/
@[path]
private lemma tprod_prime_eq_of_coeff_stabilizes_to_partial_prod_prime_eq
  [CommRing K]
-- given
  {f : ℕ → PowerSeries K}
  (hmult : IsMultipliable f)
  {limit : PowerSeries K}
  (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) limit) :
-- imply
  tprod' f hmult = limit := by
-- proof
  apply PowerSeries.tprod'_eq_of_coeffStabilizesTo_partial_prod' h hmult


-- created on 2026-10-12
