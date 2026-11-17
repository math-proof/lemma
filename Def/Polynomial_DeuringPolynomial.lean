module

public import Mathlib

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace Polynomial

noncomputable def deuringPolynomial (q : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range ((q - 1) / 2 + 1), C ((((q - 1) / 2).choose i : ℤ) ^ 2) * X ^ i

end Polynomial
