/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerPolynomialMap.lean -/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
/-!
# Integer polynomial maps

An integer polynomial map is represented by a finite family of multivariate polynomials over
`ℤ`. The definitions below provide evaluation over the integers, reduction modulo a natural
number, and iteration in the equal-dimension case.

Source: Alexander Borisov, *Iterations of Integer Polynomial Maps Modulo Primes*,
Journal of Integer Sequences 16 (2013),
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Borisov/borisov3.tex>.

JIS concept: `jis_sem_0d1bf4f3398a408e8cd23d26`.
-/


namespace MetaMathlibExt

/-- An integer polynomial map from `n` variables to `m` components. -/
def IntegerPolynomialMap (n m : ℕ) : Type :=
  Fin m → MvPolynomial (Fin n) ℤ

/-- Evaluate an integer polynomial map at an integer point. -/
noncomputable def IntegerPolynomialMap.toFun {n m : ℕ}
    (F : IntegerPolynomialMap n m) (x : Fin n → ℤ) : Fin m → ℤ :=
  fun i ↦ MvPolynomial.eval x (F i)

/-- Reduce the coefficients of an integer polynomial map modulo `p`, then evaluate it at a
point over `ZMod p`.

The definition allows an arbitrary natural modulus; the source applies it when `p` is prime.
-/
noncomputable def IntegerPolynomialMap.toFunReduce {n m : ℕ}
    (F : IntegerPolynomialMap n m) (p : ℕ) (x : Fin n → ZMod p) : Fin m → ZMod p :=
  fun i ↦ MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) (F i))

/-- Apply an integer polynomial endomap `k` times. -/
noncomputable def IntegerPolynomialMap.iterate {n : ℕ}
    (F : IntegerPolynomialMap n n) (k : ℕ) (x : Fin n → ℤ) : Fin n → ℤ :=
  Nat.iterate F.toFun k x

/-- Reduce an integer polynomial endomap modulo `p`, then apply it `k` times. -/
noncomputable def IntegerPolynomialMap.iterateReduce {n : ℕ}
    (F : IntegerPolynomialMap n n) (p k : ℕ) (x : Fin n → ZMod p) : Fin n → ZMod p :=
  Nat.iterate (F.toFunReduce p) k x

end MetaMathlibExt
