import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Add α] [Zero α]
  {d : ℕ}
-- given
  (h : s.length > d)
  (X : Tensor α (n :: s)) :
-- imply
  X.sum (d + 1) = Tensor.fromVector (X.toVector.map (·.sum d)) := by
-- proof
  rw [Tensor.sum]
  simp [h]


-- created on 2025-06-27
