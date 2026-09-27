import Lemma.Int.GeAbs
import Lemma.Nat.Gt.of.Ge.Gt


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x a : α}
-- given
  (h : |x| < a) :
-- imply
  x > -a := by
-- proof
  have h₁ := Int.GeAbs (-x)
  rw [abs_neg] at h₁
  have h₂ : x ≥ -|x| := neg_le.mp h₁
  have h₃ : -|x| > -a := neg_lt_neg h
  exact Nat.Gt.of.Ge.Gt h₂ h₃


-- created on 2026-09-26
