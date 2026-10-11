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

@[simp]
theorem P_zero (r s : R) : P r s 0 = 1 := rfl

@[simp]
theorem P_one (r s : R) : P r s 1 = X - C r := rfl

theorem P_succ_succ (r s : R) (n : ℕ) :
    P r s (n + 2) = (X - C r) * P r s (n + 1) - C s * P r s n := by
  simp [P]

@[simp]
theorem Q_zero (r s lam mu : R) : Q r s lam mu 0 = 1 := rfl

theorem Q_one (r s lam mu : R) :
    Q r s lam mu 1 = P r s 1 - C lam * P r s 0 := rfl

theorem Q_add_two (r s lam mu : R) (n : ℕ) :
    Q r s lam mu (n + 2)
      = P r s (n + 2) - C lam * P r s (n + 1) - C mu * P r s n := rfl

/-- General recurrence for `Q`, valid for all `n` (in particular no
hypothesis on `mu` is needed once shifted past the `n = 0` boundary). -/
theorem Q_recurrence (r s lam mu : R) (n : ℕ) :
    Q r s lam mu (n + 3)
      = (X - C r) * Q r s lam mu (n + 2) - C s * Q r s lam mu (n + 1) := by
  cases n with
  | zero =>
    change Q r s lam mu 3 = (X - C r) * Q r s lam mu 2 - C s * Q r s lam mu 1
    have q3 : Q r s lam mu 3
        = P r s 3 - C lam * P r s 2 - C mu * P r s 1 := rfl
    have q2 : Q r s lam mu 2
        = P r s 2 - C lam * P r s 1 - C mu * P r s 0 := rfl
    have q1 : Q r s lam mu 1 = P r s 1 - C lam * P r s 0 := rfl
    have p3 : P r s 3 = (X - C r) * P r s 2 - C s * P r s 1 := rfl
    have p2 : P r s 2 = (X - C r) * P r s 1 - C s * P r s 0 := rfl
    have p0 : P r s 0 = 1 := rfl
    have p1 : P r s 1 = X - C r := rfl
    rw [q3, q2, q1, p3, p2, p0, p1]
    ring
  | succ m =>
    have e3 : Nat.succ m + 3 = (m + 2) + 2 := by omega
    have e2 : Nat.succ m + 2 = (m + 1) + 2 := by omega
    have e1 : Nat.succ m + 1 = m + 2 := by omega
    rw [e3, e2, e1]
    rw [Q_add_two _ _ _ _ (m + 2), Q_add_two _ _ _ _ (m + 1),
      Q_add_two _ _ _ _ m]
    have pA : P r s ((m + 2) + 2)
        = (X - C r) * P r s ((m + 2) + 1) - C s * P r s (m + 2) :=
      P_succ_succ r s (m + 2)
    have pB : P r s ((m + 1) + 2)
        = (X - C r) * P r s ((m + 1) + 1) - C s * P r s (m + 1) :=
      P_succ_succ r s (m + 1)
    have pC : P r s (m + 2)
        = (X - C r) * P r s (m + 1) - C s * P r s m :=
      P_succ_succ r s m
    rw [pA, pB, pC]
    ring

end MetaMathlibExt.GeneralizedChebyshevSecondKind
