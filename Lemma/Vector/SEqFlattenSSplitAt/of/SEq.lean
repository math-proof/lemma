import Lemma.Vector.EqFlattenSplitAt
open Vector


@[main]
private lemma main
  {s s': List ℕ}
  {v : List.Vector α s.prod}
  {v' : List.Vector α s'.prod}
-- given
  (h : v ≃ v')
  (d : ℕ) :
-- imply
  (v.splitAt d).flatten ≃ (v'.splitAt d).flatten := by
-- proof
  apply (EqFlattenSplitAt v d).trans
  apply SEq.symm
  apply (EqFlattenSplitAt v' d).trans h.symm


-- created on 2025-07-25
