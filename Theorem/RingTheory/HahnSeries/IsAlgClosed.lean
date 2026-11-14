/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Theorem.FieldTheory.PuiseuxTheorem.Part6

/-!
# Algebraic closedness of rational-exponent Hahn series

This file records HahnSeries.isAlgClosed_rat, the Mathlib-style name for the
algebraic-closedness theorem proved in Theorem.FieldTheory.PuiseuxTheorem.Part6.
-/

namespace HahnSeries

/-- The field of Hahn series with rational exponents over an algebraically closed
field of characteristic zero is algebraically closed. -/
theorem isAlgClosed_rat {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] :
    IsAlgClosed (HahnSeries ℚ K) :=
  MetaMathlibExt.puiseux.hahnSeries_isAlgClosed

end HahnSeries
