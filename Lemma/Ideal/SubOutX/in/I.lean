import Mathlib
import sympy.Basic


/--
`Ideal.Quotient.out_sub`: the Quotient.out of `mk I x` differs from `x` by an element of `I`.
-/
@[path]
private lemma main
  [Ring R] (I : Ideal R) [I.IsTwoSided]
  (x : R) :
-- imply
  (Ideal.Quotient.mk I x).out - x ∈ I := by
-- proof
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

/-- Compatibility alias for Definitions callers still using `Ideal.Quotient.out_sub`. -/
lemma Ideal.Quotient.out_sub [Ring R] (I : Ideal R) [I.IsTwoSided] (x : R) :
  (Ideal.Quotient.mk I x).out - x ∈ I :=
  main I x


-- created on 2026-10-24
