/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/Taylor.lean -/


import Theorem.Algebra.Polynomial.Taylor
import Mathlib.Data.ZMod.Basic
open Polynomial


-- Abstract signature use over a general commutative ring.
example {R : Type*} [CommRing R] (f : R[X]) (a : R) :
    ∃! g : R[X],
      f = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
        g * (X - C a) ^ 2 :=
  existsUnique_taylor_remainder f a

-- Use over `ZMod 4`: this typechecks only because the theorem assumes no
-- domain hypothesis (`ZMod 4` is a commutative ring with zero divisors).
example (f : (ZMod 4)[X]) (a : ZMod 4) :
    ∃! g : (ZMod 4)[X],
      f = C (f.eval a) + C (f.derivative.eval a) * (X - C a) +
        g * (X - C a) ^ 2 :=
  existsUnique_taylor_remainder f a

-- Linear case: the unique remainder is zero.
example {R : Type*} [CommRing R] (r : R) (g : R[X])
    (h : (X : R[X]) = C ((X : R[X]).eval r) +
      C ((X : R[X]).derivative.eval r) * (X - C r) + g * (X - C r) ^ 2) :
    g = 0 := by
  have h0 : (X : R[X]) = C ((X : R[X]).eval r) +
      C ((X : R[X]).derivative.eval r) * (X - C r) +
      0 * (X - C r) ^ 2 := by
    simp only [eval_X, derivative_X, eval_one, map_one, one_mul, zero_mul,
      add_zero]
    abel
  exact (existsUnique_taylor_remainder (X : R[X]) r).unique h h0

-- Concrete quadratic case: the remainder of `X ^ 2` at `a` is `1`.
example {R : Type*} [CommRing R] (a : R) :
    (X : R[X]) ^ 2 = C ((((X : R[X]) ^ 2).eval a)) +
      C ((((X : R[X]) ^ 2).derivative.eval a)) * (X - C a) +
      1 * (X - C a) ^ 2 := by
  have e1 : ((((X : R[X]) ^ 2).eval a)) = a ^ 2 := by simp
  have e2 : ((((X : R[X]) ^ 2).derivative.eval a)) = 2 * a := by
    rw [derivative_X_pow]
    norm_num [eval_mul, eval_C, eval_pow, eval_X]
  rw [e1, e2]
  simp only [map_pow, map_mul, Polynomial.C_ofNat, one_mul]
  ring

