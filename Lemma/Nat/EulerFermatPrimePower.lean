import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.EulerFermatPrimePower
open Nat


/--
[euler_fermat_prime_power_congruence_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerFermatPrimePower.lean)
-/
@[path]
private lemma euler_fermat_prime_power_congruence_general_eq
  {a p r : ℕ}
-- given
  (hp : Nat.Prime p)
  (hr : 1 ≤ r) :
-- imply
  Nat.ModEq (p ^ r) (a ^ (p ^ r)) (a ^ (p ^ (r - 1))) := by
-- proof
  apply Nat.euler_fermat_prime_power_congruence_general hp hr

/--
[euler_fermat_prime_power_congruence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerFermatPrimePower.lean)
-/
@[path]
private lemma euler_fermat_prime_power_congruence_eq
  {a p r : ℕ}
-- given
  (ha : 0 < a)
  (hp : Nat.Prime p)
  (hr : 1 ≤ r) :
-- imply
  Nat.ModEq (p ^ r) (a ^ (p ^ r)) (a ^ (p ^ (r - 1))) := by
-- proof
  apply Nat.euler_fermat_prime_power_congruence ha hp hr


-- created on 2026-10-20
