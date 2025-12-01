import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s)
  (i : Fin s.length) 
  (d : ℤ):
-- imply
  (cast (congrArg (Tensor α) h) X).permute ⟨i, by grind⟩ d = cast (by subst h; simp) (X.permute i d) := by
-- proof
  subst h
  rfl


-- created on 2025-12-01
