import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
/-!
# Generalized Chebyshev polynomials of the second kind

Formalization of the JIS source concept: the Riordan array
`((1 - λx - μx²) / (1 + rx + sx²), x / (1 + rx + sx²))` is the coefficient
array of the generalized Chebyshev polynomials of the second kind.  There is
no Riordan-array API in Mathlib, so we capture the named polynomial family
itself in a source-faithful algebraic form over a commutative ring that
avoids square roots.

With `A = X - C r`, the modified second-kind base family `P` satisfies
`P 0 = 1`, `P 1 = A`, `P (n + 2) = A * P (n + 1) - C s * P n`, and the
generalized family is `Q n = P n - C lam * P (n - 1) - C mu * P (n - 2)`
with explicit `n = 0` and `n = 1` boundary conventions.
-/


namespace MetaMathlibExt.GeneralizedChebyshevSecondKind

open Polynomial

variable {R : Type*} [CommRing R]

/-- Modified second-kind base polynomials: `P 0 = 1`, `P 1 = X - C r`, and
`P (n + 2) = (X - C r) * P (n + 1) - C s * P n`. -/
noncomputable def P (r s : R) : ℕ → Polynomial R
  | 0 => 1
  | 1 => X - C r
  | n + 2 => (X - C r) * P r s (n + 1) - C s * P r s n

/-- Generalized Chebyshev polynomials of the second kind: `Q 0 = 1`,
`Q 1 = P 1 - C lam * P 0`, and
`Q (n + 2) = P (n + 2) - C lam * P (n + 1) - C mu * P n`. -/
noncomputable def Q (r s lam mu : R) (n : ℕ) : Polynomial R :=
  match n with
  | 0 => 1
  | 1 => P r s 1 - C lam * P r s 0
  | n + 2 => P r s (n + 2) - C lam * P r s (n + 1) - C mu * P r s n

end MetaMathlibExt.GeneralizedChebyshevSecondKind
