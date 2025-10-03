import sympy.vector.vector
import Lemma.Vector.EqArraySliceS.of.SEq.Eq.Eq
open Vector


@[main]
private lemma main
  {i s i' s' : ℕ}
-- given
  (h₀ : i = i')
  (h₁ : s = s')
  (v : List.Vector α n) :
-- imply
  v.array_slice i s ≃ v.array_slice i' s' := by
-- proof
  apply EqArraySliceS.of.SEq.Eq.Eq h₀ h₁
  simp [SEq]


-- created on 2025-05-31
-- updated on 2025-06-01
