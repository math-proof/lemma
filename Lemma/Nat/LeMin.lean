import sympy.Basic


@[main]
private lemma left
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b ≤ a := by
-- proof
  simp


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b ≤ b := by
-- proof
  simp


-- created on 2025-05-14
