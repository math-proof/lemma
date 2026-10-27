import Theorem.Data.Holor.Functions
import Theorem.Logic.SEq
import Def.Data.Holor.Defs.Part4


@[path, comm, cast]
private lemma main
  [Exp α]
  {s : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s)
  (i : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).softmax i ≃ X.softmax i := by
-- proof
  aesop


-- created on 2025-10-31
