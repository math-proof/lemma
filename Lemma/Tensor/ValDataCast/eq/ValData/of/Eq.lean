import Theorem.Data.List.Mul.Part4


@[path]
private lemma main
  {s s' : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s) :
-- imply
  (cast (congrArg (Tensor α) h) X).data.val = X.data.val := by
-- proof
  subst h
  rfl


-- created on 2026-10-07
