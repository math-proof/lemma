import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.FubiniRecurrence
open MetaMathlibExt


/--
[fubiniNumber_eq_factorial_sub_sum_signed_stirling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniRecurrence.lean)
-/
@[path]
private lemma fubiniNumber_eq_factorial_sub_sum_signed_stirling_eq
  {n : ℕ} :
-- imply
  (fubiniNumber n : ℤ) =
    (Nat.factorial n : ℤ) -
    ∑ j ∈ Finset.Icc 1 n, signedStirlingFirst n (n - j) * (fubiniNumber (n - j) : ℤ) := by
-- proof
  apply MetaMathlibExt.fubiniNumber_eq_factorial_sub_sum_signed_stirling n


-- created on 2026-10-20
