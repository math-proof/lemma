import Lemma.Nat.EqAddMulDiv
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {n d r : Z}
-- given
  (h : n % d = r) :
-- imply
  ∃ q, n = q * d + r := by
-- proof
  refine ⟨n / d, ?_⟩
  rw [← h]
  exact Eq_AddMulDiv n d


-- created on 2026-08-04
