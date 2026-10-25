/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PalindromicNarayanaNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
/-!
# Palindromic Narayana numbers

This file defines the palindromic Narayana numbers appearing in Paul Barry,
*Generalized Catalan Numbers Associated with a Family of Pascal-like Triangles*:
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Barry3/barry422.tex>.
-/


namespace MetaMathlibExt

/-- The palindromic Narayana number
`Ñ(n, k) = binomial(n, k) * binomial(n + 1, k) / (k + 1)`.

The value is taken in `ℚ` so that the displayed quotient is represented literally.
-/
def palindromicNarayanaNumber (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) * ((n + 1).choose k : ℚ) / (k + 1 : ℚ)

end MetaMathlibExt
