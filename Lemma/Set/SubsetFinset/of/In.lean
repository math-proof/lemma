import sympy.Basic


@[main]
private lemma main
  {a : α}
  {s : Set α}
-- given
  (h : a ∈ s) :
-- imply
  {a} ⊆ s := by
-- proof
  rwa [Set.singleton_subset_iff]


-- created on 2018-03-30
