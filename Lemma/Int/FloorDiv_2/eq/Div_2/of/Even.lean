import Lemma.Nat.Even.is.Any_Eq_Mul2
open Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n : ℤ}
-- given
  (h : n is even) :
-- imply
  ⌊(n : α) / 2⌋ = (n : α) / 2 := by
-- proof
  obtain ⟨k, hk⟩ := Any_Eq_Mul2.of.Even h
  rw [hk]
  have h₁ : (2 * k : α) / 2 = (k : α) := by
    field_simp
  simp [h₁]


-- created on 2019-10-10
