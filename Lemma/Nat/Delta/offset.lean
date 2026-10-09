import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite


@[path]
private lemma main
  {x y t : ℤ} :
-- imply
  KroneckerDelta x y = KroneckerDelta (x + t) (y + t) := by
-- proof
  rw [Nat.Delta.eq.Ite, Nat.Delta.eq.Ite]
  simp


-- created on 2021-12-29
