import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterSchur
open SylvesterSchur
open Nat


/--
[exists_prime_gt_and_dvd_ascFactorial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur.lean)
-/
@[path]
private lemma exists_prime_gt_and_dvd_ascFactorial_eq
  {n k : ℕ}
-- given
  (hk : 0 < k)
  (hkn : k < n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.ascFactorial k := by
-- proof
  apply Nat.exists_prime_gt_and_dvd_ascFactorial hk hkn


-- created on 2026-10-20
