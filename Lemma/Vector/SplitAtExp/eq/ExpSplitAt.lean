import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import sympy.vector.functions
open Vector


@[main]
private lemma main
  [Exp α]
  {s : List ℕ}
-- given
  (x : List.Vector α s.prod) :
-- imply
  (exp x).splitAt d = exp (x.splitAt d) := by
-- proof
  ext i j
  simp [GetExp.eq.ExpGet.fin]
  simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  rw [GetExp.eq.ExpGet.fin]


-- created on 2025-12-04
