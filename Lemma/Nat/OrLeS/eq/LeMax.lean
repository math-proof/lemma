import Lemma.Nat.Max.eq.IteLe
import Lemma.Bool.BFn_Ite.is.OrAndS
open Bool Nat


@[main]
private lemma main
  [LinearOrder α]
  {x a b : α}
-- given
  (h : x ≤ a ⊔ b) :
-- imply
  x ≤ a ∨ x ≤ b := by
-- proof
  rw [Max.eq.IteLe] at h
  rw [BFn_Ite.is.OrAndS (R := (· ≤ ·))] at h
  by_cases h_le : a ≤ b <;>
    simp [h_le] at h
  ·
    right
    assumption
  ·
    left
    assumption


-- created on 2025-05-14
