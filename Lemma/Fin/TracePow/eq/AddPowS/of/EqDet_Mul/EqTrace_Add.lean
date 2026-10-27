import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.TaylorWiles.Primes


/-- ported from external source -/
@[path]
private lemma main
  [CommRing R]
  {M : Matrix (Fin 2) (Fin 2) R}
  {α β : R}
  {k : ℕ}
-- given
  (htr : M.trace = α + β)
  (hdet : M.det = α * β) :
-- imply
  (M ^ k).trace = α ^ k + β ^ k := by
-- proof
  refine Nat.strong_induction_on k ?_
  intro k ih
  if hk0 : k = 0 then
    simp [hk0, Matrix.trace_one, one_add_one_eq_two]
  else if hk1 : k = 1 then
    simpa [hk1] using htr
  else
    rw [show k = (k - 2) + 2 by omega, Matrix.trace_pow_add_two, htr, hdet,
      ih (k - 1) (by omega), ih (k - 2) (by omega)]
    ring


-- created on 2026-10-23
