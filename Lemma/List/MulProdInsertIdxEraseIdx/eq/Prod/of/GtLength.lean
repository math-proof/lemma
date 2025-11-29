import Lemma.List.Prod.eq.MulProdEraseIdx.of.GtLength
import Lemma.List.ProdInsertIdx.eq.Prod
open List


@[main]
private lemma main
  [CommMonoid α]
  {d : ℕ}
  {s : List α}
-- given
  (h : s.length > d) :
-- imply
  ((s.eraseIdx d).insertIdx d 1).prod * s[d] = s.prod := by
-- proof
  rw [ProdInsertIdx.eq.Prod]
  rw [← Prod.eq.MulProdEraseIdx.of.GtLength h]


-- created on 2025-11-29
