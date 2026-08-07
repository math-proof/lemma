import Lemma.Set.EqUnionInter__SDiff
import Lemma.Set.Union.of.Eq.Eq
open Set


@[main]
private lemma main
  {A B C : Set α}
-- given
  (h₀ : A ∩ B = ∅)
  (h₁ : A \ B = C) :
-- imply
  A = C := by
-- proof
  have := Union.of.Eq.Eq h₀ h₁
  rw [EqUnionInter__SDiff A B] at this
  simpa using this


-- created on 2018-09-16
