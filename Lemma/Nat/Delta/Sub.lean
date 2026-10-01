import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
open Nat


@[main]
private lemma main
  {x y : ℤ} :
-- imply
  KroneckerDelta x y = KroneckerDelta (x - y) 0 := by
-- proof
  rw [Delta.eq.Ite, Delta.eq.Ite]
  simp only [sub_eq_zero]


-- created on 2021-12-29
