import sympy.Basic


@[main, comm]
private lemma main
  [LinearOrder α]
  {a b c: α} :
-- imply
  a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
-- proof
  min_assoc a b c


-- created on 2025-10-27
