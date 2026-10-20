/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TrinomialCoefficient.lean -/

import Mathlib.Algebra.Polynomial.Basic

/-!
# Trinomial coefficients

The trinomial coefficient in row `n` and column `k` is the coefficient of `X ^ k` in
`(1 + X + X ^ 2) ^ n`. Consequently it is zero when `k > 2 * n`.

Sources:

* Emanuele Munarini, *Shifting Property for Riordan, Sheffer and Connection Constants
  Matrices*, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Munarini/muna4.tex>.
* Wen-jin Woan, *The Lagrange Inversion Formula and Divisibility Properties*,
  <https://cs.uwaterloo.ca/journals/JIS/VOL10/Woan/woan655.tex>.

JIS concept: `jis_sem_ad18425839072c449c4e8a69`.
-/

namespace MetaMathlibExt

/-- The coefficient of `X ^ k` in `(1 + X + X ^ 2) ^ n`. -/
noncomputable def trinomialCoefficient (n k : ℕ) : ℕ :=
  ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ n).coeff k

end MetaMathlibExt
