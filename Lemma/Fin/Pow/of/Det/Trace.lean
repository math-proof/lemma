import Mathlib
import sympy.Basic
import Lemma.TaylorWiles.Primes


/-- ported from external source -/
@[path]
private lemma main
  [CommRing R]
  {M N : Matrix (Fin 2) (Fin 2) R}
  {k : ℕ}
-- given
  (htr : M.trace = N.trace)
  (hdet : M.det = N.det) :
-- imply
  (M ^ k).trace = (N ^ k).trace := by
-- proof
  refine Nat.strong_induction_on k ?_
  intro k ih
  if hk0 : k = 0 then
    simp [hk0]
  else if hk1 : k = 1 then
    simpa [hk1] using htr
  else
    rw [show k = (k - 2) + 2 by omega, Matrix.trace_pow_add_two, Matrix.trace_pow_add_two, htr, hdet,
      ih (k - 1) (by omega), ih (k - 2) (by omega)]


-- created on 2026-10-23
