import Lemma.Int.NeCoeS.of.Ne
open Int


@[main]
private lemma main
  [AddGroupWithOne Z]
  [CharZero Z]
  {a b : ℕ}
-- given
  (h : a ≠ b) :
-- imply
  (a : Z) ≠ (b : Z) := by
-- proof
  have h' : (a : ℤ) ≠ (b : ℤ) := by
    simp_all
  have := NeCoeS.of.Ne (R := Z) h'
  simp_all


-- created on 2025-10-16
