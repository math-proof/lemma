import sympy.Basic


@[main]
private lemma main
  {s : Set α}
-- given
  (h : ∀ e, e ∉ s) :
-- imply
  s = ∅ := by
-- proof
  aesop


-- created on 2018-03-05
