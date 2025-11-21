import Lemma.List.ProdSet__Mul_Get.eq.Mul_Prod.of.Lt_Length
import Lemma.List.TakeSet.eq.SetTake.of.Lt
open List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h_s : i < s.length)
  (h_i : i < j)
  (n : α) :
-- imply
  ((s.set i (n * s[i])).take j).prod = n * (s.take j).prod := by
-- proof
  rw [TakeSet.eq.SetTake.of.Lt h_i]
  have := ProdSet__Mul_Get.eq.Mul_Prod.of.Lt_Length (s := s.take j) (i := i) (by simp; omega) n
  simp at this
  rw [this]


-- created on 2025-11-21
