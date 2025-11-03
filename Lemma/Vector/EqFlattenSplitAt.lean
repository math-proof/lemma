import Lemma.Vector.EqFlattenUnflatten
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.Prod.eq.MulProdS
open List Vector Bool


@[main]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (d : ℕ) :
-- imply
  (v.splitAt d).flatten ≃ v := by
-- proof
  unfold List.Vector.splitAt
  simp [EqFlattenUnflatten]
  apply SEqCast.of.Eq
  apply Prod.eq.MulProdS


-- created on 2025-07-08
