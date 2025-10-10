import sympy.tensor.Basic
import stdlib.SEq
import sympy.Basic


@[main, comm 1]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : ℕ)
  (d : Fin s.length) :
-- imply
  X.repeat n d ≃ ((cast (congrArg (Tensor α) h) X).repeat n ⟨d, by simp [← h]⟩) := by
-- proof
  sorry


-- created on 2025-10-10
