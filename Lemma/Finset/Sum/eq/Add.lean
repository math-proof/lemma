import sympy.Basic


@[main]
private lemma by_parts
  [CommRing α]
  {n : ℕ}
  {f g : ℕ → α} :
-- imply
  ∑ k ∈ Finset.range (n + 1), f k * g k = f n * ∑ k ∈ Finset.range (n + 1), g k - ∑ k ∈ Finset.range n, (f (k + 1) - f k) * ∑ i ∈ Finset.range (k + 1), g i := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Finset.sum_range_succ]
    ring


@[main]
private lemma by_parts.offset
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


@[main]
private lemma doit.outer.setlimit
  [AddCommMonoid α] [DecidableEq ι]
  {a b : ι}
  {g : ι → ℕ}
  {x : ι → ℕ → α}
-- given
  (h : a ≠ b) :
-- imply
  ∑ i ∈ {a, b}, ∑ j ∈ Finset.range (g i), x i j = ∑ j ∈ Finset.range (g a), x a j + ∑ j ∈ Finset.range (g b), x b j :=
-- proof
  Finset.sum_pair h


@[main]
private lemma split.limits
  [CommRing α]
  {n : ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, x i j = ∑ i ∈ Finset.range n, x i i + ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (x i j + x j i) := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib] at *
    linear_combination ih


@[main]
private lemma split.limits.triple
  [CommRing α]
  {n : ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, x i j = ∑ i ∈ Finset.range n, x i i + ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, x i j + ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, x i j := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib] at *
    linear_combination ih


@[main]
private lemma telescope.step
  [CommRing α]
  {n d : ℕ}
  {x : ℕ → α} :
-- imply
  ∑ i ∈ Finset.range n, (x (i + d) - x i) = ∑ t ∈ Finset.range d, x (n + t) - ∑ t ∈ Finset.range d, x t := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h := (Finset.sum_range_succ' (fun t => x (n + t)) d).symm.trans (Finset.sum_range_succ (fun t => x (n + t)) d)
    simp only [add_zero] at h
    rw [Finset.sum_range_succ, ih]
    simp only [show ∀ t, n + 1 + t = n + (t + 1) by intro t; omega]
    linear_combination -h


@[main]
private lemma doit.outer
  [AddCommMonoid α]
  {a : ℕ}
  {g : ℕ → ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∑ i ∈ Finset.Ico a (a + 2), ∑ j ∈ Finset.range (g i), x i j = ∑ j ∈ Finset.range (g a), x a j + ∑ j ∈ Finset.range (g (a + 1)), x (a + 1) j := by
-- proof
  rw [Finset.sum_Ico_succ_top (show a ≤ a + 1 by omega), Finset.sum_Ico_succ_top (le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]


@[main]
private lemma doit.setlimit
  [AddCommMonoid α] [DecidableEq ι]
  {a b : ι}
  {x : ι → α}
-- given
  (h : a ≠ b) :
-- imply
  ∑ i ∈ {a, b}, x i = x a + x b :=
-- proof
  Finset.sum_pair h


@[main]
private lemma doit
  [AddCommMonoid α]
  {a : ℕ}
  {x : ℕ → α} :
-- imply
  ∑ i ∈ Finset.Ico a (a + 2), x i = x a + x (a + 1) := by
-- proof
  rw [Finset.sum_Ico_succ_top (show a ≤ a + 1 by omega), Finset.sum_Ico_succ_top (le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]


-- created on 2026-09-27
