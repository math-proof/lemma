/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DigitalBinomialTheorem.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Star

open scoped BigOperators

namespace MetaMathlibExt

/-! # Digital binomial theorem (carry-free expansion)
-/

/-- Sum of the base-2 digits of `n` (the binary digit sum). -/
def binDigitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum
end MetaMathlibExt
