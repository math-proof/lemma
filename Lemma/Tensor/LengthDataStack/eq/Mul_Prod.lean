import sympy.tensor.stack
import sympy.Basic


@[main]
private lemma main
-- given
  (f : ℕ → Tensor α s)
  (n : ℕ) :
-- imply
  ([i < n] f i).data.length = n * s.prod := by
-- proof
  simp


@[main]
private lemma fin
  {n : ℕ}
-- given
  (f : Fin n → Tensor α s):
-- imply
  ([i < n] f i).data.length = n * s.prod := by
-- proof
  simp

-- created on 2025-05-23
