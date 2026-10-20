import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ClementTwinPrimes
open MetaMathlibExt


/--
[clement_twin_prime_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ClementTwinPrimes.lean)
-/
@[path]
private lemma clement_twin_prime_criterion_eq
  :
-- imply
  ∀ (p : ℕ), 2 ≤ p →
    (Nat.Prime p ∧ Nat.Prime (p + 2) ↔
    Nat.ModEq (p * (p + 2)) (4 * (Nat.factorial (p - 1) + 1) + p) 0) := by
-- proof
  apply MetaMathlibExt.clement_twin_prime_criterion


-- created on 2026-10-20
