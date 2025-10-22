import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i d).prod = (s.take i).prod * (((s.drop i).take (d + 1)).rotate 1 ++ (s.drop i).drop (d + 1)).prod := by
-- proof
  simp_all [Permute.eq.Append_AppendRotateTakeDrop]


-- created on 2025-07-14
