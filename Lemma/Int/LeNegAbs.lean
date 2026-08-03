import Lemma.Int.Ge.of.LeNegS
import Lemma.Int.GeAbs


@[main]
private lemma main
  [AddGroup α]
  [LinearOrder α]
  [AddLeftMono α]
  [AddRightMono α]
-- given
  (x : α) :
-- imply
  x ≥ -|x| := by
-- proof
  apply Int.Ge.of.LeNegS
  have h := Int.GeAbs (-x)
  simp only [abs_neg, neg_neg] at h ⊢
  exact h


-- created on 2018-06-30
