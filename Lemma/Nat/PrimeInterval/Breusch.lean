import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeInterval.Breusch
open MathlibExt.NumberTheory.BreuschWanted
open Internal


/--
[chain_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
private lemma chain_prime_eq
  :
-- imply
  ∀ p ∈ chain, p.Prime := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.chain_prime

/--
[chain_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
private lemma chain_sorted_eq
  :
-- imply
  chain.Pairwise (· < ·) := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.chain_sorted

/--
[chain_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
private lemma chain_ratio_eq
  :
-- imply
  ∀ pr ∈ chain.zip chain.tail, 8 * pr.2 < 9 * pr.1 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.chain_ratio

/--
[chain_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
private lemma chain_getLast_eq
  :
-- imply
  chain.getLast (by decide : chain ≠ []) = 9820997 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.chain_getLast

/--
[chain_cover](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
private lemma chain_cover_eq
  {X : ℝ}
-- given
  (hlo : (53 : ℝ) ≤ X)
  (hhi : X < (9820997 : ℝ)) :
-- imply
  ∃ p : ℕ, p.Prime ∧ (X : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * X := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.chain_cover X hlo hhi

/--
[analytic_at_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
private lemma analytic_at_X_eq
  {X : ℝ}
-- given
  (hX : (5600 * 4762 / 3 : ℝ) ≤ X)
  (hU : ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) → upper_ineq n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ (X : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * X := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.analytic_at_X X hX hU

/--
[breusch_prime_interval_of_upper](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
private lemma breusch_prime_interval_of_upper_eq
  {x : ℝ}
-- given
  (hx : 48 ≤ x)
  (hU : ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) → upper_ineq n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ (x : ℝ) < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * x := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.breusch_prime_interval_of_upper x hx hU

/--
[breusch_prime_interval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch.lean)
-/
@[path]
private lemma breusch_prime_interval_eq
  :
-- imply
  ∀ x : ℝ, 48 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < (9 / 8 : ℝ) * x := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.breusch_prime_interval


-- created on 2026-10-20
