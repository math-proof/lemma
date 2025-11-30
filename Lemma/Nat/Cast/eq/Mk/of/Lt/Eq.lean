import sympy.Basic


@[main, comm]
private lemma main
-- given
  (h_n : m = n)
  (h_i : i < n) :
-- imply
  cast (congrArg Fin h_n) ⟨i, h_n ▸ h_i⟩ = ⟨i, h_i⟩ := by
-- proof
  aesop


-- created on 2025-11-27
