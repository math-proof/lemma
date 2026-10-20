import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PocklingtonPrimePowerCriterion
open MetaMathlibExt


/--
[pocklington_prime_power_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PocklingtonPrimePowerCriterion.lean)
-/
@[path]
private lemma pocklington_prime_power_criterion_eq
  {N K p e : ℕ}
-- given
  (hKpos : 0 < K)
  (hp : Nat.Prime p)
  (hN : N = K * p ^ e + 1)
  (hlt : K < p ^ e)
  (hex : ∃ a : ℕ, Nat.ModEq N (a ^ (N - 1)) 1 ∧ Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
-- imply
  Nat.Prime N := by
-- proof
  apply MetaMathlibExt.pocklington_prime_power_criterion N K p e hKpos hp hN hlt hex


-- created on 2026-10-20
