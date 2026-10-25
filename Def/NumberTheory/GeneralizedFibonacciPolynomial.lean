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

end MetaMathlibExt
