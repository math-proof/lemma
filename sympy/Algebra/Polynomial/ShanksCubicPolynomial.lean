
import Mathlib.Algebra.Polynomial.Basic

/-!
# Shanks cubic polynomial

This module formalizes the Shanks cubic polynomials (SCPs).
-/


namespace MetaMathlibExt

/-- Shanks cubic polynomial `ρ(h, -1, x) = x ^ 3 - h * x ^ 2 - (h + 3) * x - 1`.

Source concept `shanks cubic polynomial` (`jis_sem_d420b3546a20fc62825bd4f4`),
statement `jis_1715bdf9bc6d7be3f67907da` from source `jis_source_86699979507d539990484515`. -/
noncomputable def shanksCubicPolynomial {R : Type*} [Ring R] (h : R) : Polynomial R :=
  Polynomial.X ^ 3 - Polynomial.C h * Polynomial.X ^ 2 -
    Polynomial.C (h + 3) * Polynomial.X - 1

end MetaMathlibExt
