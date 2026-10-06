import Lemma.Nat.Delta.eq.Ite
import Lemma.Set.In_Finset.is.OrEqS
import sympy.functions.special.tensor_functions
import sympy.Basic

open Nat Set


@[main]
private lemma main
  {x : ℕ}
-- given
  (h : x ∈ ({0, 1} : Set ℕ)) :
-- imply
  KroneckerDelta 1 x = x := by
-- proof
  rw [Delta.eq.Ite]
  obtain rfl | rfl := OrEqS.of.In_Finset h
  · simp
  · simp


-- created on 2021-03-09
