import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch5Entry30Secondordereulerian.Part3

open Ramanujan.Part1Ch5.Entry30Secondordereulerian

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_local_coeff_zero_eq
-- given
  (a : ℕ → ℂ)
  (p : ℕ) :
-- imply
  chapter5Entry30LocalCoeff a p 0 = 1 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30LocalCoeff_zero a p

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_local_coeff_one_eq
-- given
  (a : ℕ → ℂ)
  (p : ℕ) :
-- imply
  chapter5Entry30LocalCoeff a p 1 = a p := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30LocalCoeff_one a p

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_local_coeff_of_two_le_eq
-- given
  (a : ℕ → ℂ)
  (p e : ℕ)
  (he : 2 ≤ e) :
-- imply
  chapter5Entry30LocalCoeff a p e = 0 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30LocalCoeff_of_two_le a p e he

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_coeff_of_squarefree_eq
-- given
  (a : ℕ → ℂ)
  (n : ℕ)
  (hn : n ≠ 0)
  (hsq : Squarefree n) :
-- imply
  chapter5Entry30Coeff a n = ∏ p ∈ n.primeFactors, a p := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30Coeff_of_squarefree a n hn hsq

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_coeff_of_not_squarefree_eq
-- given
  (a : ℕ → ℂ)
  (n : ℕ)
  (hn : n ≠ 0)
  (hsq : ¬Squarefree n) :
-- imply
  chapter5Entry30Coeff a n = 0 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30Coeff_of_not_squarefree a n hn hsq

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_coeff_of_ne_zero_eq
-- given
  (a : ℕ → ℂ)
  (n : ℕ)
  (hn : n ≠ 0) :
-- imply
  chapter5Entry30Coeff a n =
    if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30Coeff_of_ne_zero a n hn

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma summable_chapter5_entry30_coeff_add_two_is
-- given
  (a : ℕ → ℂ)
  (c : ℝ)
  (hc : 1 < c)
  (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
-- imply
  Summable (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.summable_chapter5Entry30Coeff_add_two a c hc ha

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_coeff_zero_eq
-- given
  (a : ℕ → ℂ) :
-- imply
  chapter5Entry30Coeff a 0 = 0 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30Coeff_zero a

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_coeff_one_eq
-- given
  (a : ℕ → ℂ) :
-- imply
  chapter5Entry30Coeff a 1 = 1 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30Coeff_one a

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_coeff_prime_eq
-- given
  (a : ℕ → ℂ)
  (p : ℕ)
  (hp : p.Prime) :
-- imply
  chapter5Entry30Coeff a p = a p := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30Coeff_prime a p hp

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_coeff_prime_pow_of_two_le_eq
-- given
  (a : ℕ → ℂ)
  (p e : ℕ)
  (hp : p.Prime)
  (he : 2 ≤ e) :
-- imply
  chapter5Entry30Coeff a (p ^ e) = 0 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30Coeff_prime_pow_of_two_le a p e hp he

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_coeff_mul_of_coprime_eq
-- given
  (a : ℕ → ℂ)
  (m n : ℕ)
  (hcop : Nat.Coprime m n) :
-- imply
  chapter5Entry30Coeff a (m * n) = chapter5Entry30Coeff a m * chapter5Entry30Coeff a n := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30Coeff_mul_of_coprime a m n hcop

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma has_prod_one_add_chapter5_entry30_coeff_is
-- given
  (a : ℕ → ℂ)
  (c : ℝ)
  (hc : 1 < c)
  (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
-- imply
  HasProd (fun p : Nat.Primes => 1 + a p)
    (1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2)) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.hasProd_one_add_chapter5Entry30Coeff a c hc ha

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_squarefree_term_def_eq
-- given
  (s : ℂ)
  (j : ℕ) :
-- imply
  chapter5Entry30SquarefreeTerm s j =
    if Squarefree (j + 1) then ((j + 1 : ℕ) : ℂ) ^ (-s) else 0 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30SquarefreeTerm_def s j

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma summable_chapter5_entry30_squarefree_term_is
-- given
  (s : ℂ)
  (hs : 1 < s.re) :
-- imply
  Summable (chapter5Entry30SquarefreeTerm s) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.summable_chapter5Entry30SquarefreeTerm s hs

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma tsum_chapter5_entry30_squarefree_term_eq
-- given
  (s : ℂ)
  (hs : 1 < s.re) :
-- imply
  (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j) =
    riemannZeta s / riemannZeta (2 * s) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.tsum_chapter5Entry30SquarefreeTerm s hs

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_odd_term_def_eq
-- given
  (s : ℂ)
  (j : ℕ) :
-- imply
  chapter5Entry30OddTerm s j =
    if Squarefree (j + 1) ∧ Odd (j + 1).primeFactors.card then
      ((j + 1 : ℕ) : ℂ) ^ (-s)
    else 0 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30OddTerm_def s j

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma summable_chapter5_entry30_odd_term_is
-- given
  (s : ℂ)
  (hs : 1 < s.re) :
-- imply
  Summable (chapter5Entry30OddTerm s) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.summable_chapter5Entry30OddTerm s hs

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma tsum_chapter5_entry30_odd_term_eq
-- given
  (s : ℂ)
  (hs : 1 < s.re) :
-- imply
  (∑' j : ℕ, chapter5Entry30OddTerm s j) =
    (riemannZeta s ^ 2 - riemannZeta (2 * s)) /
      (2 * riemannZeta s * riemannZeta (2 * s)) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.tsum_chapter5Entry30OddTerm s hs

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_non_squarefree_term_def_eq
-- given
  (s : ℂ)
  (j : ℕ) :
-- imply
  chapter5Entry30NonSquarefreeTerm s j =
    if Squarefree (j + 1) then 0 else ((j + 1 : ℕ) : ℂ) ^ (-s) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30NonSquarefreeTerm_def s j

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma summable_chapter5_entry30_non_squarefree_term_is
-- given
  (s : ℂ)
  (hs : 1 < s.re) :
-- imply
  Summable (chapter5Entry30NonSquarefreeTerm s) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.summable_chapter5Entry30NonSquarefreeTerm s hs

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma tsum_chapter5_entry30_non_squarefree_term_eq
-- given
  (s : ℂ)
  (hs : 1 < s.re) :
-- imply
  (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j) =
    riemannZeta s * (riemannZeta (2 * s) - 1) / riemannZeta (2 * s) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.tsum_chapter5Entry30NonSquarefreeTerm s hs

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma chapter5_entry30_signed_coeff_of_ne_zero_eq
-- given
  (s : ℂ)
  (n : ℕ)
  (hn : n ≠ 0) :
-- imply
  chapter5Entry30SignedCoeff s n =
    if Squarefree n then
      if Odd n.primeFactors.card then -((n : ℂ) ^ (-s))
      else (n : ℂ) ^ (-s)
    else 0 := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.chapter5Entry30SignedCoeff_of_ne_zero s n hn

/--
[Part1Ch5Entry30Secondordereulerian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry30Secondordereulerian.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry30_second_order_eulerian_is :
-- imply
  (∀ (a : ℕ → ℂ) (c : ℝ), 1 < c →
    (∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) →
      Summable (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) ∧
      (∀ n : ℕ, n ≠ 0 →
        chapter5Entry30Coeff a n =
          if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0) ∧
      HasProd (fun p : Nat.Primes => 1 + a p)
        (1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2))) ∧
  ∀ s : ℂ, 1 < s.re →
    (∀ n : ℕ, n ≠ 0 →
      chapter5Entry30SignedCoeff s n =
        if Squarefree n then
          if Odd n.primeFactors.card then -((n : ℂ) ^ (-s))
          else (n : ℂ) ^ (-s)
        else 0) ∧
    riemannZeta s ≠ 0 ∧
    riemannZeta (2 * s) ≠ 0 ∧
    Summable (chapter5Entry30SquarefreeTerm s) ∧
    (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j) =
      riemannZeta s / riemannZeta (2 * s) ∧
    Summable (chapter5Entry30OddTerm s) ∧
    (∑' j : ℕ, chapter5Entry30OddTerm s j) =
      (riemannZeta s ^ 2 - riemannZeta (2 * s)) /
        (2 * riemannZeta s * riemannZeta (2 * s)) ∧
    Summable (chapter5Entry30NonSquarefreeTerm s) ∧
    (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j) =
      riemannZeta s * (riemannZeta (2 * s) - 1) /
        riemannZeta (2 * s) := by
-- proof
  apply Ramanujan.Part1Ch5.Entry30Secondordereulerian.ramanujan_part1_ch5_entry30_secondordereulerian

-- created on 2026-10-10
