import Def.Data.Holor.Relu


@[path]
private lemma main
  {k n m : ℤ}
-- given
  (h₀ : k ≤ n) :
-- imply
  relu (k - min m n) = relu (k - m) := by
-- proof
  unfold relu
  if hmn : m ≤ n then
    simp [min_eq_left hmn]
  else
    have hnm : n ≤ m := le_of_not_ge hmn
    have hk : k - n ≤ 0 := by
      linarith
    have hkm : k - m ≤ 0 := by
      linarith
    simp [min_eq_right hnm, max_eq_right hk, max_eq_right hkm]


-- created on 2021-12-25
-- updated on 2026-10-26
