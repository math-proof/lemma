import sympy.tensor.tensor
import sympy.Basic


@[main]
private lemma main
-- given
  (d : Fin s.length)
  (i : Fin s[d])
  (a : α) :
-- imply
  (⟨List.Vector.replicate s.prod a⟩ : Tensor α s).select d i = ⟨List.Vector.replicate (s.eraseIdx d).prod a⟩ := by
-- proof
  sorry


-- created on 2025-12-01
