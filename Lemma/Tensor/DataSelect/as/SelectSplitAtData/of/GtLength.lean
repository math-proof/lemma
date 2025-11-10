import stdlib.SEq
import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_d : s.length > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.select ⟨d, h_d⟩ i).data ≃ (X.data.splitAt (d + 1))[i :: s[d]].flatten := by
-- proof
  sorry


-- created on 2025-11-10
