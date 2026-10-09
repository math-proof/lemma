import Lemma.Set.In_Ico.of.And.split.Ico


@[path]
private lemma main
  {x a b d : ℤ}
-- given
  (h : x ∈ Range a b d) :
-- imply
  x ∈ Range a b (Int.sign d) ∧ x % d = a % d := by
-- proof
  exact Set.In_Ico.of.And.split.Ico h


-- created on 2023-05-30
