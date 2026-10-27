import Theorem.Logic.SEq
import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Sum
@[path, cast]
private lemma main
  [Add α] [Zero α]
-- given
  (h : s = s')
  (X : Tensor α s)
  (i : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).sum i ≃ X.sum i := by
-- proof
  subst h
  rfl


-- created on 2025-10-31
