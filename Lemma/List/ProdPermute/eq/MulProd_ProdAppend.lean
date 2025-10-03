import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.ProdAppend.eq.MulProdS
open List


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (d : Fin s.length)
  (k : ℕ) :
-- imply
  (s.permute d k).prod = (s.take d).prod * (((s.drop d).take (k + 1)).rotate 1 ++ (s.drop d).drop (k + 1)).prod := by
-- proof
  simp_all [Permute.eq.Append_AppendRotateTakeDrop]


-- created on 2025-07-14
