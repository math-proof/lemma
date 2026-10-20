import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.BonseInequality
open Finset
open MetaMathlibExt


/--
[bonse_primes_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
private lemma bonse_primes_infinite_eq
  :
-- imply
  (Set.ofPred fun p : ℕ => Prime p).Infinite := by
-- proof
  apply MetaMathlibExt.bonse_primes_infinite

/--
[bonse_nth_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
private lemma bonse_nth_strictMono_eq
  :
-- imply
  StrictMono (Nat.nth Prime) := by
-- proof
  apply MetaMathlibExt.bonse_nth_strictMono

/--
[bonse_nth_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
private lemma bonse_nth_prime_eq
  {k : ℕ} :
-- imply
  Prime (Nat.nth Prime k) := by
-- proof
  apply MetaMathlibExt.bonse_nth_prime k

/--
[bonse_nth_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
private lemma bonse_nth_five_eq
  :
-- imply
  Nat.nth Prime 5 = 13 := by
-- proof
  apply MetaMathlibExt.bonse_nth_five

/--
[bonse_nth_succ_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
private lemma bonse_nth_succ_lt_eq
  {k : ℕ} :
-- imply
  Nat.nth Prime (k + 1) < 2 * Nat.nth Prime k := by
-- proof
  apply MetaMathlibExt.bonse_nth_succ_lt k

/--
[bonse_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
private lemma bonse_inequality_eq
  {k : ℕ}
-- given
  (hk : 4 < k) :
-- imply
  (Nat.nth Prime k) ^ 2 < ∏ i ∈ Finset.range k, Nat.nth Prime i := by
-- proof
  apply MetaMathlibExt.bonse_inequality k hk


-- created on 2026-10-20
