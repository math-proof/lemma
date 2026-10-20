import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.TangentNumberDivisibility
open MetaMathlibExt


/--
[tangentNumber_two_adic_divisibility_mod_six](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TangentNumberDivisibility.lean)
-/
@[path]
private lemma tangentNumber_two_adic_divisibility_mod_six_eq
  {T : ℕ → ℤ}
  {n : ℕ}
-- given
  (hT_zero : T 0 = 0)
  (hT_succ : ∀ m : ℕ, T (m + 1) = (if m = 0 then 1 else 0) - ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * T k * T (m - k))
  (hn : 1 ≤ n) :
-- imply
  ((2 : ℤ) ^ n ∣ T (2 * n + 1)) ∧
    Int.ModEq 6 (T (2 * n + 1) / (2 : ℤ) ^ n)
    ((-1 : ℤ) ^ n * 4 ^ (n - 1)) := by
-- proof
  apply MetaMathlibExt.tangentNumber_two_adic_divisibility_mod_six T hT_zero hT_succ n hn


-- created on 2026-10-20
