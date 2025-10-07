import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∀ x : α, p x ∧ q x)
  (left : Bool := true) :
-- imply
  match left with
  | true =>
    ∀ x : α, p x
  | false =>
    ∀ x : α, q x := by
-- proof
  match left with
  | true =>
    intro x
    exact (h x).left
  | false =>
    intro x
    exact (h x).right


-- created on 2024-07-01
