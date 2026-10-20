/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanLarcombeFrenchNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Catalan-Larcombe-French numbers

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex>.
-/

namespace MetaMathlibExt

/-- Catalan-Larcombe-French numbers (OEIS A053175):
`P n = 2 ^ n * ∑ k ≤ n, C(n, 2 * k) * C(2 * k, k) ^ 2 * 4 ^ (n - 2 * k)`.

Source concept `jis_sem_503660cf82b130f1605e9f7a`, statement
`jis_1e931a28e8b97599583c6b62`. -/
def catalanLarcombeFrenchNumber : ℕ → ℕ :=
  fun n => 2 ^ n * Finset.sum (Finset.range (n + 1)) fun k =>
    Nat.choose n (2 * k) * Nat.choose (2 * k) k ^ 2 * 4 ^ (n - 2 * k)

end MetaMathlibExt
