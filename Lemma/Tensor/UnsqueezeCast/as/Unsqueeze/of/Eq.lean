import stdlib.SEq
import sympy.tensor.Basic


@[main, comm, cast]
private lemma main
  {s : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).unsqueeze d ≃ X.unsqueeze d := by
-- proof
  subst h
  rfl


-- created on 2025-10-10
