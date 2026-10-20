import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry1Corollary1BinomialSeries
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry1Corollary1BinomialSeries


/--
[ramanujan_part1_ch3_entry1_corollary1_binomial_series_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1Corollary1BinomialSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry1_corollary1_binomial_series_general_eq
  {n x : ℂ}
  {Q : ℕ → ℂ}
-- given
  (hx : ‖x‖ < 1)
  (hsum : Summable (fun p : ℕ × ℕ => Q p.1 * (∏ j ∈ Finset.range (p.1 + p.2), (n - (j : ℂ))) * x ^ (p.1 + p.2) / (Nat.factorial p.2 : ℂ))) :
-- imply
  ∃ s : ℂ,
    HasSum (fun k : ℕ => (∑ j ∈ Finset.range (k + 1), Q j / (Nat.factorial (k - j) : ℂ)) *
    (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k) s ∧
    HasSum (fun k : ℕ => Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k *
    Complex.exp ((n - (k : ℂ)) * Complex.log (1 + x))) s := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1Corollary1BinomialSeries.ramanujan_part1_ch3_entry1_corollary1_binomial_series_general n x Q hx hsum

/--
[ramanujan_part1_ch3_entry1_corollary1_binomial_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1Corollary1BinomialSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry1_corollary1_binomial_series_eq
  {n x : ℂ}
  {Q : ℕ → ℂ}
-- given
  (hx : ‖x‖ < 1)
  (hQ : ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, ‖z‖ < R → Summable (fun k : ℕ => Q k * z ^ k))
  (hsum : Summable (fun p : ℕ × ℕ => Q p.1 * (∏ j ∈ Finset.range (p.1 + p.2), (n - (j : ℂ))) * x ^ (p.1 + p.2) / (Nat.factorial p.2 : ℂ))) :
-- imply
  ∃ s : ℂ,
    HasSum (fun k : ℕ => (∑ j ∈ Finset.range (k + 1), Q j / (Nat.factorial (k - j) : ℂ)) *
    (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k) s ∧
    HasSum (fun k : ℕ => Q k * (∏ j ∈ Finset.range k, (n - (j : ℂ))) * x ^ k *
    Complex.exp ((n - (k : ℂ)) * Complex.log (1 + x))) s := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1Corollary1BinomialSeries.ramanujan_part1_ch3_entry1_corollary1_binomial_series n x Q hx hQ hsum


-- created on 2026-10-20
