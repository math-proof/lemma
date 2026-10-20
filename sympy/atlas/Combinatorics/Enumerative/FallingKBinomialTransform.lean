/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FallingKBinomialTransform.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Falling k-binomial transforms

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL10/French/french13.tex>.
-/

open scoped BigOperators

namespace MetaMathlibExt

/-- Falling `k`-binomial transform of a sequence:
`b n = ∑ i ∈ range (n + 1), C(n, i) * k ^ (n - i) * a i`.

Source statement `jis_f80f56d96d180cdfb88089a0`, concept
`jis_sem_435054dc88f9efa6e6529e6a`. -/
def fallingKBinomialTransform (k : ℤ) (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * k ^ (n - i) * a i

/-- Binomial transform of a sequence, the `k = 1` case of
`fallingKBinomialTransform`. -/
def binomialTransform (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  fallingKBinomialTransform 1 a n

/-- The `k = 1` falling `k`-binomial transform has the usual binomial sum. -/
theorem binomialTransform_eq_sum (a : ℕ → ℤ) (n : ℕ) :
    binomialTransform a n =
      ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * a i := by
  simp [binomialTransform, fallingKBinomialTransform, one_pow, mul_one]

end MetaMathlibExt
