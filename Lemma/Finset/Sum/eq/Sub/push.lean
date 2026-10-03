import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α]
  {f : ℤ → α}
  {a b : ℤ}
-- given
  (h : a ≤ b) :
-- imply
  ∑ i ∈ Finset.Ico a b, f i = (∑ i ∈ Finset.Ico a (b + 1), f i) - f b := by
-- proof
  have hs : ∑ i ∈ Finset.Ico a (b + 1), f i = (∑ i ∈ Finset.Ico a b, f i) + f b := by
    rw [←Finset.insert_Ico_right_eq_Ico_add_one h, Finset.sum_insert (by simp), add_comm]
  rw [hs, add_sub_cancel_right]


-- created on 2026-10-03
