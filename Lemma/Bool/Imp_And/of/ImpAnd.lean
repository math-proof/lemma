import sympy.Basic


@[main]
private lemma left
  {p q r: Prop}
-- given
  (h : p ∧ q → r) :
-- imply
  p ∧ q → p ∧ r :=
-- proof
  fun h_pq =>
    ⟨h_pq.left, h h_pq⟩


@[main]
private lemma main
  {p q r: Prop}
-- given
  (h : p ∧ q → r) :
-- imply
  p ∧ q → r ∧ q :=
-- proof
  fun h_pq =>
    ⟨h h_pq, h_pq.right⟩


-- created on 2025-01-12
