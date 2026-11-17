/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DigitalBinomialTheorem.lean -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Star

@[expose] public section

open scoped BigOperators


namespace MetaMathlibExt

/-! # Digital binomial theorem (carry-free expansion)
-/

/-- Sum of the base-2 digits of `n` (the binary digit sum). -/
def binDigitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

end MetaMathlibExt
