import Mathlib.Analysis.Complex.Trigonometric
import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
import sympy.Basic

open Nat


@[path]
private lemma main
  [DecidableEq α]
  {x : ℂ}
  {i j : α} :
-- imply
  Complex.sin (x * (KroneckerDelta i j : ℂ)) =
      (KroneckerDelta i j : ℂ) * Complex.sin x := by
-- proof
  simp only [Delta.eq.Ite i j, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  split_ifs <;> simp


-- created on 2023-06-08
