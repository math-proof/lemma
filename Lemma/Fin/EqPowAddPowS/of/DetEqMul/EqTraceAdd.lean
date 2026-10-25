import Mathlib
import sympy.Basic
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
  induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k with
      | 0 => simp [Matrix.trace_one, one_add_one_eq_two]
      | 1 => simpa using htr
      | (k + 2) =>
        rw [Matrix.trace_pow_add_two, htr, hdet, ih (k + 1) (by omega), ih k (by omega)]
        ring


-- created on 2026-10-23
