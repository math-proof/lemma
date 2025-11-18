import sympy.Basic
import sympy.tensor.functions


@[main, comm]
private lemma main
  [Exp α]
-- given
  (h_k : s.length > k)
  (h_d : k > d)
  (X : Tensor α s)
  (i : Fin s[d]) :
-- imply
  (X.softmax k).select ⟨d, by omega⟩ i = (X.select ⟨d, by omega⟩ i).softmax (k - 1) := by
-- proof
  sorry


-- created on 2025-11-17
