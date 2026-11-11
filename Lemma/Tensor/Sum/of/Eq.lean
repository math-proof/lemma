import Def.Data.Tensor.Defs.Part4
import Def.Data.Tensor.Sum


@[path]
private lemma main
  [Add α] [Zero α]
  {A B : Tensor α s}
-- given
  (h : A = B)
  (i : ℕ) :
-- imply
  A.sum i = B.sum i := by
-- proof
  subst h
  simp


-- created on 2020-08-26
