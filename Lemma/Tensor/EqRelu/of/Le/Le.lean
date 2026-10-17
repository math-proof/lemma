import torch.nn.functional.relu
import sympy.Basic


@[path]
private lemma main
  {k n m : ℤ}
-- given
  (h₀ : k ≤ n)
  (h₁ : min m n ≤ k) :
-- imply
  k - min m n = relu (k - m) := by
-- proof
  unfold relu
  if hmn : m ≤ n then
    have hkm : m ≤ k := by
      simpa [min_eq_left hmn] using h₁
    simp [min_eq_left hmn, max_eq_left (sub_nonneg.mpr hkm)]
  else
    have hnm : n ≤ m := le_of_not_ge hmn
    have hk : k = n := by
      have hkn : n ≤ k := by
        simpa [min_eq_right hnm] using h₁
      linarith
    rw [min_eq_right hnm, hk]
    have hkm : n - m ≤ 0 := by
      linarith
    rw [max_eq_right hkm]
    ring


-- created on 2026-10-11
-- updated on 2026-10-17
