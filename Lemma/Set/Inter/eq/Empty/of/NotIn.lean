import sympy.Basic


@[main]
private lemma main
  {a : α}
  {B : Set α}
-- given
  (h : a ∉ B) :
-- imply
  {a} ∩ B = ∅ :=
-- proof
  Set.singleton_inter_eq_empty.mpr h


-- created on 2026-09-27
