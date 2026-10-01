import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid β]
  {p : Prop} [Decidable p]
  {s : Finset ι}
  {f g : ι → β} :
-- imply
  ∑ i ∈ s, (if p then f i else g i) = if p then ∑ i ∈ s, f i else ∑ i ∈ s, g i := by
-- proof
  by_cases hp : p <;> simp [hp]


@[main]
private lemma pop
  {a b : ℤ}
  {f : ℤ → ℝ} :
-- imply
  ∑ i ∈ Finset.Ico a b, f i = if a ≤ b - 1 then ∑ i ∈ Finset.Ico a (b - 1), f i + f (b - 1) else 0 := by
-- proof
  split_ifs with h
  ·
    have e : Finset.Ico a b = insert (b - 1) (Finset.Ico a (b - 1)) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [e, Finset.sum_insert (by simp), add_comm]
  ·
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]


@[main]
private lemma unshift
  {a b : ℤ}
  {f : ℤ → ℝ} :
-- imply
  ∑ i ∈ Finset.Ico a b, f i = if b ≥ a then ∑ i ∈ Finset.Ico (a - 1) b, f i - f (a - 1) else 0 := by
-- proof
  split_ifs with h
  ·
    have e : Finset.Ico (a - 1) b = insert (a - 1) (Finset.Ico a b) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [e, Finset.sum_insert (by simp), add_sub_cancel_left]
  ·
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]


-- created on 2020-03-17
