import stdlib.SEq
import sympy.tensor.tensor
import sympy.Basic


@[main]
private lemma main
  {s s' : List ℕ}
-- given
  (h_s : s' = s)
  (X : Tensor α s)
  (dim : Fin s.length)
  (i : Fin s[dim]) :
-- imply
  have h : Tensor α s = Tensor α s' := by rw [h_s]
  (cast h X).getEllipsis ⟨dim, by simp_all⟩ ⟨i, by simp_all⟩ ≃ X.getEllipsis dim i := by
-- proof
  constructor <;>
    aesop


-- created on 2025-10-05
