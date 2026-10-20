/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HankelTransform.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Hankel transforms

This module defines the zero-indexed Hankel transform of a sequence. Its `n`-th term is the
determinant of the `(n + 1) × (n + 1)` Hankel matrix, whose `(i, j)` entry is `a (i + j)`.

Sources:

* <https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry4/barry122.tex>
* <https://cs.uwaterloo.ca/journals/JIS/VOL10/French/french13.tex>

JIS concept: `jis_sem_44db93a38a920ba88ba59880`.
-/

namespace MetaMathlibExt

/-- The Hankel transform of `a`, indexed so that term `n` is the determinant of the
`(n + 1) × (n + 1)` matrix with entry `a (i + j)` in position `(i, j)`. -/
def hankelTransform {R : Type*} [CommRing R] (a : ℕ → R) : ℕ → R :=
  fun n ↦ Matrix.det (Matrix.of fun i j : Fin (n + 1) ↦ a (i.val + j.val))

/-- Algebraic tail-witness predicate for a Jacobi continued fraction: the head
equation pins the numerator `mu0`, and each tail factor has linear term
`alpha i` and shifted quadratic numerator `beta (i + 1) x^2`, with minus signs.
This is only the algebraic boundary, not Heilermann's determinant identity.
Source: Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel
Transforms," JIS 24 (2021), Article 21.10.2,
`https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex`, lines 110-117
(source SHA-256 `9cd9826f06a6786a792c651fa1f84a8e2bb5b365fb8b57234a78b87714935f51`;
lines 110-117 SHA-256 `11385eb5eee1af1081307348d4029cdc74b51d84e8bff2fbe9831891145d998e`).
JIS concept: `jis_dep_heilermann_049f63eb`. -/
def HasJacobiFraction {K : Type*} [Ring K] (a alpha beta : ℕ → K) (mu0 : K)
    (F : ℕ → PowerSeries K) : Prop :=
  PowerSeries.mk a = PowerSeries.C mu0 * F 0 ∧
    ∀ i : ℕ,
      (1 - PowerSeries.C (alpha i) * PowerSeries.X -
        PowerSeries.C (beta (i + 1)) * PowerSeries.X ^ 2 * F (i + 1)) * F i = 1

end MetaMathlibExt
