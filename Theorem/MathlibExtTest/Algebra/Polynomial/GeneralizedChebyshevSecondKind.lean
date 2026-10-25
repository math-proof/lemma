/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/GeneralizedChebyshevSecondKind.lean -/

import Theorem.Algebra.Polynomial.GeneralizedChebyshevSecondKind
import Mathlib.Tactic
open Polynomial MetaMathlibExt.GeneralizedChebyshevSecondKind

variable {R : Type*} [CommRing R]


-- Base family boundary values.
example (r s : R) : P r s 0 = 1 := P_zero _ _

example (r s : R) : P r s 1 = X - C r := P_one _ _

example (r s : R) : P r s 2 = (X - C r) * (X - C r) - C s * 1 := rfl

-- Generalized family boundary values at `n = 0` and `n = 1`.
example (r s lam mu : R) : Q r s lam mu 0 = 1 := Q_zero _ _ _ _

example (r s lam mu : R) : Q r s lam mu 1 = (X - C r) - C lam := by
  rw [Q_one, P_one, P_zero, mul_one]

-- Closed form at `n = 2` (all source parameters occur).
example (r s lam mu : R) :
    Q r s lam mu 2
      = ((X - C r) * (X - C r) - C s * 1) - C lam * (X - C r) - C mu * 1 := rfl

-- General recurrence, instantiated at `n = 0` (hence covering `n = 3`).
example (r s lam mu : R) :
    Q r s lam mu 3 = (X - C r) * Q r s lam mu 2 - C s * Q r s lam mu 1 :=
  Q_recurrence _ _ _ _ 0

-- General recurrence in full generality.
example (r s lam mu : R) (n : ℕ) :
    Q r s lam mu (n + 3)
      = (X - C r) * Q r s lam mu (n + 2) - C s * Q r s lam mu (n + 1) :=
  Q_recurrence _ _ _ _ n

-- Source example specialization `r = 0`, `s = 1`, `lam = -1`, `mu = 0`.
example : Q (0 : R) 1 (-1) 0 0 = 1 := Q_zero _ _ _ _

example : Q (0 : R) 1 (-1) 0 1 = X + 1 := by
  rw [Q_one, P_one, P_zero, map_zero, map_neg, map_one, sub_zero, mul_one,
    sub_neg_eq_add]

example (n : ℕ) :
    Q (0 : R) 1 (-1) 0 (n + 2)
      = X * Q (0 : R) 1 (-1) 0 (n + 1) - Q (0 : R) 1 (-1) 0 n := by
  cases n with
  | zero =>
    have q2 : Q (0 : R) 1 (-1) 0 2
        = P (0 : R) 1 2 - C (-1 : R) * P (0 : R) 1 1
          - C (0 : R) * P (0 : R) 1 0 :=
      Q_add_two _ _ _ _ 0
    have q1 : Q (0 : R) 1 (-1) 0 1
        = P (0 : R) 1 1 - C (-1 : R) * P (0 : R) 1 0 :=
      Q_one _ _ _ _
    have q0 : Q (0 : R) 1 (-1) 0 0 = 1 := Q_zero _ _ _ _
    have p2 : P (0 : R) 1 2
        = (X - C (0 : R)) * P (0 : R) 1 1 - C (1 : R) * P (0 : R) 1 0 :=
      P_succ_succ _ _ 0
    have p1 : P (0 : R) 1 1 = X - C (0 : R) := P_one _ _
    have p0 : P (0 : R) 1 0 = 1 := P_zero _ _
    rw [q2, q1, q0, p2, p1, p0, map_zero, map_neg, map_one]
    ring
  | succ m =>
    have h := Q_recurrence (0 : R) 1 (-1) 0 m
    have eL : Nat.succ m + 2 = m + 3 := by omega
    have eM : Nat.succ m + 1 = m + 2 := by omega
    rw [eL, eM, h, map_zero, sub_zero, map_one, one_mul]

