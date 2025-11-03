import Lemma.List.DvdProdSDrop
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  [CommMonoid Z]
-- given
  (h : i ≥ j)
  (s : List Z) :
-- imply
  (s.drop i).prod ∣ (s.drop j).prod := by
-- proof
  have := DvdProdSDrop s j (i - j)
  rw [EqAdd_Sub.of.Ge h] at this
  assumption


-- created on 2025-11-03
