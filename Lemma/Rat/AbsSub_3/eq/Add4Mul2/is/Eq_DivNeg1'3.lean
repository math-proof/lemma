import Lemma.Nat.EqMax.is.OrAndS
open Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (x : α) :
-- imply
  |x - 3| = 4 + 2 * x ↔ x = -1 / 3 := by
-- proof
  rw [abs_eq_max_neg]
  constructor <;>
    intro h
  ·
    obtain h₀ | h₁ := OrAndS.of.EqMax h <;>
      linarith
  ·
    rw [h]
    norm_num


-- created on 2025-03-31
-- updated on 2025-08-02
