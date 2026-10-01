import sympy.Basic
import Mathlib.Data.Matrix.Basic
open Matrix


@[main]
private lemma main
  {n : ℕ}
  {x : ℂ}
  {f g : ℂ → Matrix (Fin n) (Fin n) ℂ}
-- given
  (h : f x = g x) :
-- imply
  (f x)ᵀ = (g x)ᵀ := by
-- proof
  rw [h]


-- created on 2022-01-11
