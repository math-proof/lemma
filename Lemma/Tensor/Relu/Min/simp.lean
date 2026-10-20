import torch.nn.functional.relu


@[path]
private lemma main
  {k n l : ℤ}
-- given
  (h₀ : k ≤ n) :
-- imply
  relu (k - min l n) = relu (k - l) := by
-- proof
  unfold relu
  if hln : l ≤ n then
    simp [min_eq_left hln]
  else
    have hnl : n ≤ l := le_of_not_ge hln
    have hk : k - n ≤ 0 := by
      linarith
    have hkl : k - l ≤ 0 := by
      linarith
    simp [min_eq_right hnl, max_eq_right hk, max_eq_right hkl]


-- created on 2021-12-25
-- updated on 2026-10-17
