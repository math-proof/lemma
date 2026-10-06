import Mathlib
import sympy.Basic

open Polynomial
open Matrix

/--
[Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one.lean)
-/

private lemma  pow_five_aux
    {R : Type*}
    [CommRing R]
    (g : Matrix (Fin 2) (Fin 2) R) (hdet : g.det = 1)
    (ht : g.trace ^ 2 + g.trace - 1 = 0) : g ^ 5 = 1 := by
  nontriviality R
  set t := g.trace with ht_def
  have e1 : (C t : R[X]) ^ 4 - 3 * C t ^ 2 + 1 = 0 := by
    have : t ^ 4 - 3 * t ^ 2 + 1 = 0 := by linear_combination (t ^ 2 - t - 1) * ht
    have h__af := (congrArg (C : R → R[X]) this)
    simp at h__af
    exact h__af
  have e2 : (C t : R[X]) ^ 3 - 2 * C t + 1 = 0 := by
    have : t ^ 3 - 2 * t + 1 = 0 := by linear_combination (t - 1) * ht
    have h__af := (congrArg (C : R → R[X]) this)
    simp at h__af
    exact h__af
  have key : (X ^ 5 - 1 : R[X]) =
      g.charpoly * (X ^ 3 + C t * X ^ 2 + (C t ^ 2 - 1) * X + (C t ^ 3 - 2 * C t)) := by
    rw [Matrix.charpoly_fin_two, hdet, map_one]
    linear_combination X * e1 - e2
  have h := Matrix.aeval_self_charpoly g
  have : aeval g (X ^ 5 - 1 : R[X]) = 0 := by rw [key, map_mul, h, zero_mul]
  simpa [sub_eq_zero] using this
@[main]
private lemma main
  [CommRing R]
  {g : Matrix (Fin 2) (Fin 2) R}
-- given
  (hdet : g.det = 1)
  (ht : g.trace ^ 2 + g.trace - 1 = 0) :
-- imply
  g ^ 5 = 1 :=
-- proof
  pow_five_aux g hdet ht


-- created on 2026-10-05
