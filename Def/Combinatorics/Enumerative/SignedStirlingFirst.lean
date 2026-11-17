/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- `signedStirlingFirst n k = (-1)^(n-k) s(n,k)` with `s` the unsigned first-kind Stirling
number. -/
def signedStirlingFirst : ℕ → ℕ → ℤ :=
  fun n k => (-1 : ℤ) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

end MetaMathlibExt
