import stdlib.SEq
import sympy.tensor.tensor
import sympy.Basic


@[main]
private lemma main
-- given
  (h_s : s = s')
  (X : Tensor α s)
  (dim : Fin s.length)
  (i : Fin s[dim]) :
-- imply
  (cast (congrArg (Tensor α) h_s) X).select ⟨dim, by grind⟩ ⟨i, by aesop⟩ ≃ X.select dim i := by
-- proof
  aesop


-- created on 2025-10-05
