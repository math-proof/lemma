import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PellCassiniIdentity
open MetaMathlibExt


/--
[pell_cassini_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PellCassiniIdentity.lean)
-/
@[path]
private lemma pell_cassini_identity_eq
  {P : ℕ → ℕ}
  {k : ℕ}
-- given
  (hP_zero : P 0 = 0)
  (hP_one : P 1 = 1)
  (hP_step : ∀ n : ℕ, P (n + 2) = 2 * P (n + 1) + P n)
  (hk : 1 ≤ k) :
-- imply
  (P (k - 1) : ℤ) * (P (k + 1) : ℤ) =
      (P k : ℤ) ^ 2 + (-1 : ℤ) ^ k := by
-- proof
  apply MetaMathlibExt.pell_cassini_identity P hP_zero hP_one hP_step k hk


-- created on 2026-10-20
