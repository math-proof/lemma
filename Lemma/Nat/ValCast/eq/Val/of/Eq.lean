import sympy.Basic


@[main]
private lemma main
-- given
  (h_n : m = n)
  (i : Fin m) :
-- imply
  cast (congrArg Fin h_n) i = i.val := by
-- proof
  aesop


-- created on 2025-11-28
