import stdlib.SEq
import sympy.tensor.Basic


@[main, cast]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : ℕ)
  (d : Fin s.length) :
-- imply
  (cast (congrArg (Tensor α) h) X).repeat ⟨d, by simp [← h]⟩ n ≃ X.repeat d n := by
-- proof
  subst h
  rfl


-- created on 2025-10-10
