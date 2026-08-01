import Lemma.Bool.Imp.is.OrNot


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p) :
-- imply
  q → p := by
-- proof
  simp [h]


-- created on 2019-06-30
