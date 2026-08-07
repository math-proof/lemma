import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
open Vector


@[main, comm]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (d : ℕ)
  (f : α → β) :
-- imply
  (v.map f).splitAt d = (v.splitAt d).map (·.map f) := by
-- proof
  ext q r
  simp [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]


-- created on 2026-08-07
