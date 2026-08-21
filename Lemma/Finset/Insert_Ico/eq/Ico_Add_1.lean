import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  [LinearOrder α] [One α] [LocallyFiniteOrder α] [Add α] [SuccAddOrder α] [NoMaxOrder α]
  {a b : α}
-- given
  (h : a ≤ b) :
-- imply
  insert b (Finset.Ico a b) = Finset.Ico a (b + 1) :=
-- proof
  Finset.insert_Ico_right_eq_Ico_add_one h


-- created on 2026-08-05
