import sympy.Basic


@[path]
private lemma main
  [AddCommGroup α]
  {f : ℤ → α}
  {a b : ℤ}
-- given
  (h : a ≤ b) :
-- imply
  ∑ i ∈ Finset.Ico a b, f i = (∑ i ∈ Finset.Ico (a - 1) b, f i) - f (a - 1) := by
-- proof
  have hp : (Order.pred a : ℤ) = a - 1 := by simp
  have hs : ∑ i ∈ Finset.Ico (a - 1) b, f i = f (a - 1) + ∑ i ∈ Finset.Ico a b, f i := by
    rw [← hp, ← Finset.insert_Ico_left_eq_Ico_pred h, Finset.sum_insert (by simp)]
  rw [hs, add_sub_cancel_left]


-- created on 2019-11-04
-- updated on 2023-03-30
