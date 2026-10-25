/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HighlyComposite.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc


namespace Nat

/-!
# Highly composite numbers

This file formalizes the strict divisor records and their first shape theorem from
*Prime-Exponent Transition Geometry and Divisor Barriers Between Consecutive Highly
Composite Numbers* (arXiv:2608.17045), `hcn_transition_geometry.tex`, source SHA-256
`f8de59657076caf6f78a5e97cbdde69afd23b0c6dafc3e790d098cb9ef58aa42`, lines 121–127
and 250–270.
-/

/-- A positive natural number is highly composite if it has strictly more divisors than every
smaller positive natural number. -/
def IsHighlyComposite (H : ℕ) : Prop :=
  0 < H ∧ ∀ m : ℕ, 0 < m → m < H → m.divisors.card < H.divisors.card

end Nat
