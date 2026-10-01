import sympy.Basic


@[main]
private lemma main
  [Zero α]
  [LinearOrder α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a > 0 ∨ a < 0 :=
-- proof
  (lt_or_gt_of_ne h).symm


-- created on 2023-05-02
