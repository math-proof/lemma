import sympy.Basic


@[main]
private lemma main
  [DecidableEq α] [AddCommMonoid β]
  {A B : Finset α}
  {f : α → β}
-- given
  (h : A ∩ B = ∅) :
-- imply
  ∑ x ∈ A ∪ B, f x = ∑ x ∈ A, f x + ∑ x ∈ B, f x :=
-- proof
  Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr h)


-- created on 2026-09-27
