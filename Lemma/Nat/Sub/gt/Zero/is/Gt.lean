import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddCommMonoid α] [LinearOrder α] [CanonicallyOrderedAdd α] [Sub α] [OrderedSub α]
  {a b : α} :
-- imply
  b - a > 0 ↔ b > a :=
-- proof
  tsub_pos_iff_lt


-- created on 2025-10-16
