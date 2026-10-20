import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimePowerFactorizationSum
open MetaMathlibExt


/--
[prime_power_factorization_sum_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimePowerFactorizationSum.lean)
-/
@[path]
private lemma prime_power_factorization_sum_eq_iff_eq
  {p m s y : ℕ}
-- given
  (hp : Nat.Prime p)
  (hm : 0 < m)
  (hs : 0 < s)
  (hy : y = p ^ m) :
-- imply
  (y.factorization.sum fun q e => e * q ^ s) = y ↔
      ∃ k : ℕ, m = p ^ k ∧ s = p ^ k - k := by
-- proof
  apply MetaMathlibExt.prime_power_factorization_sum_eq_iff hp hm hs hy


-- created on 2026-10-20
