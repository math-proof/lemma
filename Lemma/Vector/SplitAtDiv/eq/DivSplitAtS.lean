import sympy.vector.vector
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetDiv.eq.DivGetS
open Vector


@[main]
private lemma main
  [Div α]
  {s : List ℕ}
-- given
  (a b : List.Vector α s.prod) :
-- imply
  (a / b).splitAt d = a.splitAt d / b.splitAt d := by
-- proof
  ext i j
  repeat rw [GetDiv.eq.DivGetS.fin]
  repeat rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  rw [GetDiv.eq.DivGetS.fin]


-- created on 2025-10-08
