import stdlib.SEq
import sympy.tensor.tensor


@[main]
private lemma main
  {d k : ℕ}
-- given
  (h_k : s.length > k)
  (h_d : k > d)
  (X : Tensor α s)
  (i : Fin s[d])
  (n : ℕ) :
-- imply
  (X.repeat n ⟨k, h_k⟩).select ⟨d, by grind⟩ ⟨i, by grind⟩ ≃ (X.select ⟨d, by grind⟩ i).repeat n ⟨k - 1, by grind⟩ := by
-- proof
  -- Tensor.SelectRepeat.as.RepeatSelect.of.Lt
  sorry


-- created on 2025-11-29
