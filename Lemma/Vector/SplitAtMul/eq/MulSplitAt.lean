import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
open Vector


@[main]
private lemma main
  [Mul α]
  {s : List ℕ}
-- given
  (x : List.Vector α s.prod)
  (a : α)
  (d : ℕ) :
-- imply
  (x * a).splitAt d = x.splitAt d * List.Vector.replicate (s.drop d).prod a := by
-- proof
  ext q r
  simp [GetMul.eq.MulGet.fin]
  simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  simp [GetMul.eq.MulGet.fin]
  simp [GetMul.eq.MulGetS.fin]
  simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]


-- created on 2025-12-01
