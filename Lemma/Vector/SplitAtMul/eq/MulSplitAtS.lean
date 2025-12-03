import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
open Vector


@[main]
private lemma main
  [Mul α]
  {s : List ℕ}
-- given
  (a b : List.Vector α s.prod)
  (d : ℕ) :
-- imply
  (a * b).splitAt d = a.splitAt d * b.splitAt d := by
-- proof
  ext q r
  simp [GetMul.eq.MulGetS.fin]
  simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  simp [GetMul.eq.MulGetS.fin]


-- created on 2025-12-03
