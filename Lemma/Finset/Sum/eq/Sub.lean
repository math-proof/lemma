import sympy.Basic


@[main]
private lemma telescope
  [AddCommGroup α]
  {a b : ℕ}
  {x : ℕ → α}
-- given
  (h : a ≤ b) :
-- imply
  ∑ k ∈ Finset.Ico a b, (x (k + 1) - x k) = x b - x a := by
-- proof
  induction b, h using Nat.le_induction with
  | base =>
    simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih]
    abel


@[main]
private lemma unshift
  [AddCommGroup α]
  {a b : ℕ}
  {f : ℕ → α}
-- given
  (h : a + 1 ≤ b) :
-- imply
  ∑ i ∈ Finset.Ico (a + 1) b, f i = ∑ i ∈ Finset.Ico a b, f i - f a := by
-- proof
  rw [Finset.sum_eq_sum_Ico_succ_bot (show a < b by omega)]
  abel


@[main]
private lemma push
  [AddCommGroup α]
  {a b : ℕ}
  {f : ℕ → α}
-- given
  (h : a ≤ b) :
-- imply
  ∑ i ∈ Finset.Ico a b, f i = ∑ i ∈ Finset.Ico a (b + 1), f i - f b := by
-- proof
  rw [Finset.sum_Ico_succ_top h]
  abel


-- created on 2019-11-07
