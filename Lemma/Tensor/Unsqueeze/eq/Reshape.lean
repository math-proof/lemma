import Lemma.Bool.Cast.of.SEq.Eq
import Def.Data.Holor.Prod
import Lemma.Vector.SEqRepeat_Div
import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Reshape
import Def.Data.Holor.Unsqueeze
open Bool List Vector


@[path, comm]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.unsqueeze d = X.reshape (s.insertIdx d 1) (by simp [Prod.eq.ProdInsertIdx s d]) := by
-- proof
  simp [Tensor.unsqueeze]


-- created on 2026-07-12
