import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
  (left : Bool := true)
-- given
  (h : match left with
       | true => p
       | false => q) :
-- imply
  p ∨ q := by
-- proof
  cases left with
  | true =>
    exact Or.inl h
  | false =>
    exact Or.inr h


-- created on 2026-10-03
