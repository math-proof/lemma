import sympy.core.mul
import sympy.Basic


@[main]
private lemma main
  {n m : ℕ}
-- given
  (h : n = m)
  (v : List.Vector α n) :
-- imply
  (cast (congrArg (List.Vector α) h) v).val = v.val := by
-- proof
  subst h
  rfl


-- created on 2026-10-07
