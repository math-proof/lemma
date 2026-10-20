import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.PellBinomialTransform
open MetaMathlibExt


/--
[pell_binomial_transform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PellBinomialTransform.lean)
-/
@[path]
private lemma pell_binomial_transform_eq
  {P : ℕ → ℤ}
  {n : ℕ}
-- given
  (h0 : P 0 = 0)
  (h1 : P 1 = 1)
  (hrec : ∀ n, P (n + 2) = 2 * P (n + 1) + P n) :
-- imply
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) * P i =
    ∑ k ∈ Finset.range (n + 1),
    (if k % 2 = 0 then (0 : ℤ) else if k % 8 = 1 ∨ k % 8 = 7 then 1 else -1) *
    ((2 * n).choose (n + k) : ℤ) := by
-- proof
  apply MetaMathlibExt.pell_binomial_transform P h0 h1 hrec n


-- created on 2026-10-20
