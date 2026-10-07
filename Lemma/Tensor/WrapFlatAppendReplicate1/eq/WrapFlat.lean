import sympy.core.mul
import sympy.Basic
open Tensor


@[main]
private lemma main
-- given
  (s out : List ℕ)
  (k i : ℕ) :
-- imply
  wrapFlat (List.replicate k 1 ++ s) (List.replicate k 1 ++ out) i =
      wrapFlat s out i := by
-- proof
  induction k with
  | zero =>
    simp
  | succ k ih =>
    simp [List.replicate_succ, wrapFlat, Nat.mod_one, ih]


-- created on 2026-10-07
