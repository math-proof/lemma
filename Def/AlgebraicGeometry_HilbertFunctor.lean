import Mathlib

set_option autoImplicit false

namespace AlgebraicGeometry.HilbertFunctor

open MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ}


variable (A n)


variable {A}


noncomputable def hilbertFunctionOf (P : Polynomial ℚ) (D₀ : ℕ) : ℕ → ℕ :=
  fun d => if d < D₀ then Nat.choose (n + d) n else Int.toNat ⌊P.eval (d : ℚ)⌋

end AlgebraicGeometry.HilbertFunctor
