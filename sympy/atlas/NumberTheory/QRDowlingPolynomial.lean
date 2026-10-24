/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QRDowlingPolynomial.lean -/

import Mathlib.Algebra.Polynomial.Eval.Defs

open scoped BigOperators

namespace MetaMathlibExt

variable {R : Type*} [Semiring R]

/-!
Provenance for the `(q, r)`-Dowling polynomial and number:

- lexical concept `jis_term_a2bc80130d1209c8dec31ca0`;
- semantic concept `jis_sem_21a4a5cbb99f9b622432388e`;
- source statements `jis_936d415cbd90fe97c847cf81` and `jis_8910e171ff1cd000908e919c`;
- JIS VOL18/Mangontarum,
  <https://cs.uwaterloo.ca/journals/JIS/VOL18/Mangontarum/mango2.tex>, SHA-256
  `7eeb8709f4c547fa50ca7b8eb6a005b9b58e0a3e0ff3befac5c3db7c5b23bda1`;
- JIS VOL20/Mangontarum,
  <https://cs.uwaterloo.ca/journals/JIS/VOL20/Mangontarum/mango4.tex>, SHA-256
  `3e6c2cf946c933cf36388d5da99293ed8f39d50de0024290beb39f94ccaa5c5d`.
-/

/-- The `(q, r)`-Dowling polynomial associated to a fixed family `W` of
`(q, r)`-Whitney coefficients of the second kind. -/
noncomputable def qrDowlingPolynomial (W : ℕ → ℕ → R) (n : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (W n k) * Polynomial.X ^ k

/-- The `(q, r)`-Dowling number is the associated polynomial evaluated at `1`. -/
noncomputable def qrDowlingNumber (W : ℕ → ℕ → R) (n : ℕ) : R :=
  Polynomial.eval 1 (qrDowlingPolynomial W n)
end MetaMathlibExt
