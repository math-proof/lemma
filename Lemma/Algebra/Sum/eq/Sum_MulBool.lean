import Lemma.Bool.Bool.eq.Ite
open Bool


@[main]
private lemma main
  [NonAssocSemiring β]
  [Fintype α]
  [DecidableEq α]
-- given
  (A : Finset α)
  (f : α → β) :
-- imply
  ∑ x ∈ A, f x = ∑ x, Bool.toNat (x ∈ A) * f x := by
-- proof
  simp [Bool.eq.Ite]


-- created on 2025-07-19
