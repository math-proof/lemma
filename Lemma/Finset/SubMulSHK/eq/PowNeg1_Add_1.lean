import sympy.concrete.continued_fraction
import sympy.Basic
open Continuant


@[path]
private lemma main
  [CommRing R]
-- given
  (x : ℕ → R)
  (n : ℕ) :
-- imply
  H x (n + 1) * K x n - H x n * K x (n + 1) = (-1) ^ (n + 1) := by
-- proof
  induction n with
  | zero => simp [H, K]
  | succ n ih =>
    show (H x (n + 1) * x (n + 1) + H x n) * K x (n + 1) - H x (n + 1) * (K x (n + 1) * x (n + 1) + K x n) =
      (-1) ^ (n + 1 + 1)
    rw [pow_succ]
    linear_combination (-1 : R) * ih


-- created on 2026-10-07
