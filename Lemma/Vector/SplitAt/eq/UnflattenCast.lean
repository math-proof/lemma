import sympy.vector.vector
import Lemma.List.Prod.eq.MulProdTake__ProdDrop
open List


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (d : ℕ) :
-- imply
  v.splitAt d = (cast (congrArg (List.Vector α) (Prod.eq.MulProdTake__ProdDrop s d)) v).unflatten := by
-- proof
  simp [List.Vector.splitAt]


-- created on 2025-07-12
