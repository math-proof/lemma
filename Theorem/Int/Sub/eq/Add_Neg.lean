module

public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Int.Sub.eq.Add_Neg
  [SubNegMonoid α]
-- given
  (a b : α) :
-- imply
  a - b = a + -b :=
-- proof
  sub_eq_add_neg a b


-- created on 2024-07-01
-- updated on 2026-10-26
