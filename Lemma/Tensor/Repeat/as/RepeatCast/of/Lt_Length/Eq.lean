import stdlib.SEq
import sympy.tensor.Basic



@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s = s')
  (h_d : d < s.length)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X.repeat n ⟨d, h_d⟩ ≃ (cast (congrArg (Tensor α) h) X).repeat n ⟨d, by simpa [← h]⟩ := by
-- proof
  subst h
  rfl


-- created on 2025-10-10
