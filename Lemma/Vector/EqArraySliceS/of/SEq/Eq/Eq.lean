import stdlib.SEq
import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
  {v : List.Vector α n}
  {v' : List.Vector α n'}
  {i s i' s' : ℕ}
-- given
  (h₀ : i = i')
  (h₁ : s = s')
  (h₂ : v ≃ v') :
-- imply
  v.array_slice i s ≃ v'.array_slice i' s' := by
-- proof
  simp [SEq] at *
  constructor
  .
    simp_all
  .
    congr <;>
      simp_all


-- created on 2025-05-31
