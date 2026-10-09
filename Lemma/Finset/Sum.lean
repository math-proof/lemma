import sympy.Basic


@[path]
private lemma limits.delete.baseset
  [Fintype ι] [DecidableEq ι] [AddCommMonoid α]
  {A : Finset ι}
  {p : ι → Prop} [DecidablePred p]
  {f : ι → α} :
-- imply
  ∑ x ∈ A.filter p, f x = ∑ x ∈ Finset.univ.filter (fun x => p x ∧ x ∈ A), f x := by
-- proof
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext x
  simp [and_comm]


@[path]
private lemma doit.inner
  [AddCommMonoid α]
  {a m : ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.Ico a (a + 2), x i j = ∑ i ∈ Finset.range m, (x i a + x i (a + 1)) := by
-- proof
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_Ico_succ_top (show a ≤ a + 1 by omega), Finset.sum_Ico_succ_top (le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]


@[path]
private lemma limits.swap.intlimit.parallel
  [AddCommMonoid α]
  {a m d n : ℤ}
  {f : ℤ → ℤ → α} :
-- imply
  ∑ j ∈ Finset.Ico a m, ∑ i ∈ Finset.Ico (j + d) (j + n), f i j = ∑ i ∈ Finset.Ico (a + d) (m + n - 1), ∑ j ∈ Finset.Ico (max a (i - n + 1)) (min m (i - d + 1)), f i j := by
-- proof
  apply Finset.sum_comm'
  intro j i
  simp only [Finset.mem_Ico, max_le_iff, lt_min_iff]
  omega


@[path]
private lemma doit.inner.setlimit
  [AddCommMonoid α] [DecidableEq ι]
  {a b : ι}
  {m : ℕ}
  {x : ℕ → ι → α}
-- given
  (h : a ≠ b) :
-- imply
  ∑ i ∈ Finset.range m, ∑ j ∈ {a, b}, x i j = ∑ i ∈ Finset.range m, (x i a + x i b) := by
-- proof
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_pair h]


@[path]
private lemma limits.swap.intlimit
  [AddCommMonoid α]
  {a d n : ℤ}
  {f : ℤ → ℤ → α} :
-- imply
  ∑ j ∈ Finset.Ico a (n - d), ∑ i ∈ Finset.Ico (j + d) n, f i j = ∑ i ∈ Finset.Ico (a + d) n, ∑ j ∈ Finset.Ico a (i - d + 1), f i j := by
-- proof
  apply Finset.sum_comm'
  intro j i
  simp only [Finset.mem_Ico]
  omega


@[path]
private lemma limits.swap.subst
  [AddCommMonoid α]
  {A : Finset ι}
  {s : ι → Finset κ}
  {f : κ → ι → α} :
-- imply
  ∑ j ∈ A, ∑ i ∈ s j, f i j = ∑ i ∈ A, ∑ j ∈ s i, f j i :=
-- proof
  rfl


@[path]
private lemma doit.outer.setlimit
  [AddCommMonoid α]
  {a : ι}
  {g : ι → ℕ}
  {x : ι → ℕ → α} :
-- imply
  ∑ i ∈ {a}, ∑ j ∈ Finset.range (g i), x i j = ∑ j ∈ Finset.range (g a), x a j :=
-- proof
  Finset.sum_singleton _ _


@[path]
private lemma limits.separate
  [CommSemiring α]
  {s t : Finset ι}
  {f : ι → α}
  {g : ι → ι → α} :
-- imply
  ∑ j ∈ s, ∑ i ∈ t, f j * g i j = ∑ j ∈ s, f j * ∑ i ∈ t, g i j := by
-- proof
  simp only [Finset.mul_sum]


-- created on 2026-09-27
