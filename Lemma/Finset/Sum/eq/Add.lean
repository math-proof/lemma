import Initialize.Tactic.Attr.Basic


@[path]
private lemma by_parts
  [CommRing α]
  {n : ℕ}
  {f g : ℕ → α} :
-- imply
  ∑ k < (n + 1), f k * g k = f n * ∑ k < (n + 1), g k - ∑ k < n, (f (k + 1) - f k) * ∑ i < (k + 1), g i := by
-- proof
  simp only [Nat.Iio_eq_range]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Finset.sum_range_succ]
    ring

@[path]
private lemma by_parts_offset
  [CommRing α]
  {i n : ℕ}
  {f g : ℕ → α}
-- given
  (h : i ≤ n) :
-- imply
  ∑ k ∈ Finset.Ico i (n + 1), f k * g k = f n * ∑ k ∈ Finset.Ico i (n + 1), g k - ∑ k ∈ Finset.Ico i n, (f (k + 1) - f k) * ∑ j ∈ Finset.Ico i (k + 1), g j := by
-- proof
  induction n, h using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top (show i ≤ m + 1 by omega), ih, Finset.sum_Ico_succ_top (show i ≤ m + 1 by omega) g, Finset.sum_Ico_succ_top hm (fun k => (f (k + 1) - f k) * ∑ j ∈ Finset.Ico i (k + 1), g j)]
    ring

@[path]
private lemma doit_outer_setlimit
  [AddCommMonoid α] [DecidableEq ι]
  {a b : ι}
  {g : ι → ℕ}
  {x : ι → ℕ → α}
-- given
  (h : a ≠ b) :
-- imply
  ∑ i ∈ {a, b}, ∑ j < (g i), x i j = ∑ j < (g a), x a j + ∑ j < (g b), x b j :=
-- proof
  Finset.sum_pair h

@[path]
private lemma split_limits
  [CommRing α]
  {n : ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∑ i < n, ∑ j < n, x i j = ∑ i < n, x i i + ∑ i < n, ∑ j < i, (x i j + x j i) := by
-- proof
  simp only [Nat.Iio_eq_range]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib] at *
    linear_combination ih

@[path]
private lemma split_limits_triple
  [CommRing α]
  {n : ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∑ i < n, ∑ j < n, x i j = ∑ i < n, x i i + ∑ i < n, ∑ j < i, x i j + ∑ j < n, ∑ i < j, x i j := by
-- proof
  simp only [Nat.Iio_eq_range]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib] at *
    linear_combination ih

@[path]
private lemma telescope_step
  [CommRing α]
  {n d : ℕ}
  {x : ℕ → α} :
-- imply
  ∑ i < n, (x (i + d) - x i) = ∑ t < d, x (n + t) - ∑ t < d, x t := by
-- proof
  simp only [Nat.Iio_eq_range]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h := (Finset.sum_range_succ' (fun t => x (n + t)) d).symm.trans (Finset.sum_range_succ (fun t => x (n + t)) d)
    simp only [add_zero] at h
    rw [Finset.sum_range_succ, ih]
    simp only [show ∀ t, n + 1 + t = n + (t + 1) by intro t; omega]
    linear_combination -h

@[path]
private lemma doit_outer
  [AddCommMonoid α]
  {a : ℕ}
  {g : ℕ → ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∑ i ∈ Finset.Ico a (a + 2), ∑ j < (g i), x i j = ∑ j < (g a), x a j + ∑ j < (g (a + 1)), x (a + 1) j := by
-- proof
  rw [Finset.sum_Ico_succ_top (show a ≤ a + 1 by omega), Finset.sum_Ico_succ_top (le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]

@[path]
private lemma doit_setlimit
  [AddCommMonoid α] [DecidableEq ι]
  {a b : ι}
  {x : ι → α}
-- given
  (h : a ≠ b) :
-- imply
  ∑ i ∈ {a, b}, x i = x a + x b :=
-- proof
  Finset.sum_pair h

@[path]
private lemma doit
  [AddCommMonoid α]
  {a : ℕ}
  {x : ℕ → α} :
-- imply
  ∑ i ∈ Finset.Ico a (a + 2), x i = x a + x (a + 1) := by
-- proof
  rw [Finset.sum_Ico_succ_top (show a ≤ a + 1 by omega), Finset.sum_Ico_succ_top (le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]


-- created on 2026-09-27
-- updated on 2026-11-26
