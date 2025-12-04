import Lemma.Vector.GetNeg.eq.NegGet
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
open Vector


@[main]
private lemma main
  [Neg α]
  {s : List ℕ}
-- given
  (x : List.Vector α s.prod) :
-- imply
  (-x).splitAt d = -x.splitAt d := by
-- proof
  ext i j
  simp [GetNeg.eq.NegGet.fin]
  simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  rw [GetNeg.eq.NegGet.fin]


-- created on 2025-12-04
