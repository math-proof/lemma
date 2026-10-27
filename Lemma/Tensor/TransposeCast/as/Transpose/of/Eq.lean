import Theorem.Logic.SEq
import Def.Data.Holor.Defs.Part4
import Notation.Data.Holor.Permute


@[path, cast]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s)
  (i j : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).transpose i j ≃ X.transpose i j := by
-- proof
  subst h
  rfl


-- created on 2026-07-11
-- updated on 2026-10-26
