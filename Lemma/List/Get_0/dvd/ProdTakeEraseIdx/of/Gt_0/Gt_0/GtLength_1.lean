import Lemma.List.EqEraseIdx.of.Ge_Length
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.Get_0.dvd.ProdTake.of.Gt_0.GtLength_0
import Lemma.List.ProdCons.eq.Mul_Prod
import Lemma.List.Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0
open List


@[main]
private lemma main
  [Monoid M]
  {s : List M}
-- given
  (h_s : s.length > 1)
  (h_d : d > 0)
  (h_i : i > 0) :
-- imply
  s[0] ∣ ((s.eraseIdx i).take d).prod := by
-- proof
  if h_length : i < s.length then
    rw [Take.eq.Cons_TakeTail.of.Gt_0.GtLength_0 _ h_d]
    ·
      rw [ProdCons.eq.Mul_Prod]
      rw [GetEraseIdx.eq.Get.of.Gt.GtLength h_length h_i]
      simp
    ·
      grind
  else
    simp at h_length
    rw [EqEraseIdx.of.Ge_Length h_length]
    exact Get_0.dvd.ProdTake.of.Gt_0.GtLength_0 _ h_d


-- created on 2025-11-04
