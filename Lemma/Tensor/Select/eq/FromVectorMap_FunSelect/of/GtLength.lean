import sympy.tensor.tensor


@[main]
private lemma main
  {d : ℕ}
-- given
  (h : s.length > d)
  (i : Fin s[d])
  (X : Tensor α (n :: s)) :
-- imply
  X.select ⟨d + 1, by grind⟩ ⟨i, by grind⟩ = Tensor.fromVector (X.toVector.map (·.select ⟨d, by grind⟩ i)) := by
-- proof
  rw [Tensor.select]
  simp_all


-- created on 2025-11-15
