import Lemma.List.TakePermute.eq.RotateTake.of.Lt_Length
import Lemma.List.ProdRotate.eq.Prod
open List


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : d < s.length) :
-- imply
  ((s.permute ⟨0, by grind⟩ d).take (d + 1)).prod = (s.take (d + 1)).prod := by
-- proof
  rw [TakePermute.eq.RotateTake.of.Lt_Length h]
  rw [ProdRotate.eq.Prod]


-- created on 2025-10-22
