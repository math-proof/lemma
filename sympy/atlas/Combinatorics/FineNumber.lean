/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/FineNumber.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs

namespace MetaMathlibExt

/-- Fine numbers (OEIS A000957), zero-based: `fineNumber n` is source `𝔽_(n+1)`.

Source explicit formula `𝔽_n = (1/n) * ∑_{i=1}^n (-2)^(i-1) * i * C(2n, n-i)`
with `𝔽_1 = 1`, from JIS VOL21/Janjic3/janjic96.tex lines 105-108 and 157-158.
Phrase concept `jis_term_dfac4b97dfaf92729d46eb23`; source statement
`jis_5d8bd849271ecf8ace5bbc6f`; source URL
`https://cs.uwaterloo.ca/journals/JIS/VOL21/Janjic3/janjic96.tex`. -/
def fineNumber (n : Nat) : ℚ :=
  (1 / ((n : ℚ) + 1)) * ∑ i ∈ Finset.range (n + 1),
    (-2 : ℚ) ^ i * ((i : ℚ) + 1) * ((Nat.choose (2 * (n + 1)) (n - i) : ℕ) : ℚ)

/-- Restatement of the exact source explicit formula for the Fine numbers. -/
theorem fineNumber_eq_sum (n : Nat) :
    fineNumber n = (1 / ((n : ℚ) + 1)) * ∑ i ∈ Finset.range (n + 1),
      (-2 : ℚ) ^ i * ((i : ℚ) + 1) * ((Nat.choose (2 * (n + 1)) (n - i) : ℕ) : ℚ) :=
  rfl

end MetaMathlibExt
