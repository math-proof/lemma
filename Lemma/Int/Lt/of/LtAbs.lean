import Lemma.Int.GeAbs
import Lemma.Nat.Lt.of.Le.Lt


@[main]
private lemma main
  [AddGroup α] [LinearOrder α]
  {x a : α}
-- given
  (h : |x| < a) :
-- imply
  x < a := by
-- proof
  have h₁ := Int.GeAbs x
  exact Nat.Lt.of.Le.Lt h₁ h


-- created on 2026-09-26
