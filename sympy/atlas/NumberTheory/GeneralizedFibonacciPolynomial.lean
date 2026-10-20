/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibonacciPolynomial.lean -/

import Mathlib.Algebra.Polynomial.Basic

/-!
Provenance: concept `jis_sem_f9bc27c2fb50e959e168b460`
(`generalized Fibonacci polynomial sequence`); source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general` from
`jis_source_f9d72107307ec9892cf536d9`.
-/

namespace MetaMathlibExt

/-- Generalized Fibonacci polynomial sequence with parameters in `ℤ[X]`.

Concept `jis_sem_f9bc27c2fb50e959e168b460`; source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general`
(clauses `coefficient_domain`, `initial_zero`, `initial_one`, `recurrence`). -/
noncomputable def generalizedFibonacciPolynomial
    (p0 p1 d g : Polynomial ℤ) : ℕ → Polynomial ℤ
  | 0 => p0
  | 1 => p1
  | (n + 2) =>
    d * generalizedFibonacciPolynomial p0 p1 d g (n + 1) +
      g * generalizedFibonacciPolynomial p0 p1 d g n

/-- Value at `0`: `G_0 = p0`.

Concept `jis_sem_f9bc27c2fb50e959e168b460`; source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general`
(clause `initial_zero`). -/
@[simp]
theorem generalizedFibonacciPolynomial_zero
    (p0 p1 d g : Polynomial ℤ) :
    generalizedFibonacciPolynomial p0 p1 d g 0 = p0 := rfl

/-- Value at `1`: `G_1 = p1`.

Concept `jis_sem_f9bc27c2fb50e959e168b460`; source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general`
(clause `initial_one`). -/
@[simp]
theorem generalizedFibonacciPolynomial_one
    (p0 p1 d g : Polynomial ℤ) :
    generalizedFibonacciPolynomial p0 p1 d g 1 = p1 := rfl

/-- Recurrence: `G_{n+2} = d * G_{n+1} + g * G_n`.

Concept `jis_sem_f9bc27c2fb50e959e168b460`; source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general`
(clause `recurrence`). -/
@[simp]
theorem generalizedFibonacciPolynomial_add_two
    (p0 p1 d g : Polynomial ℤ) (n : ℕ) :
    generalizedFibonacciPolynomial p0 p1 d g (n + 2) =
      d * generalizedFibonacciPolynomial p0 p1 d g (n + 1) +
        g * generalizedFibonacciPolynomial p0 p1 d g n := rfl

end MetaMathlibExt
