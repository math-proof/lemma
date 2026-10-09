import sympy.Basic


@[path]
private lemma main
  {a : α}
  {B : Set α}
-- given
  (h : a ∉ B) :
-- imply
  {a} ∩ B = ∅ :=
-- proof
  Set.singleton_inter_eq_empty.mpr h


-- created on 2019-02-02
