import sympy.tensor.Basic
import Lemma.Basic


@[main]
private lemma main
  [Add α] [Zero α]
  {dim : ℕ}
-- given
  (h : dim < s.length)
  (X : Tensor α (n :: s)) :
-- imply
  X.sum (dim + 1) = Tensor.fromVector (X.toVector.map (·.sum dim)) := by
-- proof
  rw [Tensor.sum]
  simp [h]


-- created on 2025-06-27
