import stdlib.SEq
import sympy.tensor.Basic



@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s = s')
  (h_d : s.length > d)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.repeat ⟨d, h_d⟩ n ≃ (cast (congrArg (Tensor α) h) X).repeat ⟨d, by simpa [← h]⟩ n := by
-- proof
  subst h
  rfl


-- created on 2025-10-10
