import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterSchur.ErdosLayers
open scoped BigOperators
open Finset Nat
open Nat.SylvesterSchur


/--
[pow_mul_choose_le_pow_mul_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosLayers.lean)
-/
@[path]
private lemma pow_mul_choose_le_pow_mul_choose_eq
  {M N r : ℕ}
-- given
  (hrM : r ≤ M)
  (hMN : M ≤ N) :
-- imply
  N ^ r * Nat.choose M r ≤ M ^ r * Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.pow_mul_choose_le_pow_mul_choose hrM hMN

/--
[exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_div_three_layers_lt_lower_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosLayers.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_div_three_layers_lt_lower_pow_eq
  {N r : ℕ}
-- given
  (hN : 0 < N)
  (hrN : r ≤ N)
  (h2rN : 2 * r ≤ N)
  (hN6 : 6 ≤ N)
  (hbound : r ! * (∏ j ∈ Finset.range (Nat.log 2 N), if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) < (N + 1 - r) ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_factorial_mul_prod_erdos_div_three_layers_lt_lower_pow hN hrN h2rN hN6 hbound

/--
[exists_large_prime_dvd_choose_of_mul_prod_erdos_div_three_layers_lt_four_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosLayers.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_mul_prod_erdos_div_three_layers_lt_four_pow_eq
  {N r : ℕ}
-- given
  (hr : 4 ≤ r)
  (h2rN : 2 * r ≤ N)
  (hN6 : 6 ≤ N)
  (hbound : r * (∏ j ∈ Finset.range (Nat.log 2 N), if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) < 4 ^ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_mul_prod_erdos_div_three_layers_lt_four_pow hr h2rN hN6 hbound


-- created on 2026-10-20
