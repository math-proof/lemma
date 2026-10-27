import Theorem.Logic.SEq
import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Unsqueeze


@[path, comm, cast]
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
