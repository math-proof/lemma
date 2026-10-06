import sympy.Basic
import Mathlib


@[main]
private lemma main
  {a : α}
  {B : Set α}
-- given
  (h : ({a} : Set α) ∩ B = ∅) :
-- imply
  a ∉ B :=
-- proof
  Set.disjoint_singleton_left.mp (Set.disjoint_iff_inter_eq_empty.mpr h)


-- created on 2019-02-02
