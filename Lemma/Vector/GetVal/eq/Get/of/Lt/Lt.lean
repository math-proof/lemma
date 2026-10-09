import sympy.core.mul
import sympy.Basic


@[path]
private lemma main
  {i : ℕ}
-- given
  (v : List.Vector α n)
  (hi : i < n)
  (_ : i < v.val.length) :
-- imply
  v.val[i] = v.get ⟨i, hi⟩ := by
-- proof
  exact rfl


-- created on 2026-10-07
