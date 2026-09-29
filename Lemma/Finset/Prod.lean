import sympy.sets.sets
import sympy.Basic


@[main]
private lemma doit.inner
  [CommMonoid α]
  {m : ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range 5, x i j = ∏ i ∈ Finset.range m, (x i 0 * x i 1 * x i 2 * x i 3 * x i 4) := by
-- proof
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]


@[main]
private lemma doit.inner.setlimit
  [CommMonoid α]
  {m : ℕ}
  {x : ℕ → ℕ → α} :
-- imply
  ∏ i ∈ Finset.range m, ∏ j ∈ ({0, 1, 2, 3} : Finset ℕ), x i j = ∏ i ∈ Finset.range m, (x i 0 * x i 1 * x i 2 * x i 3) := by
-- proof
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  simp only [mul_assoc]


@[main]
private lemma doit.outer.setlimit
  [CommMonoid α]
  {a : ι}
  {f g : ι → ℕ}
  {x : ι → ℕ → ℕ → α} :
-- imply
  ∏ i ∈ {a}, ∏ j ∈ Finset.range (f i), ∏ k ∈ Finset.range (g i), x i j k = ∏ j ∈ Finset.range (f a), ∏ k ∈ Finset.range (g a), x a j k := by
-- proof
  exact Finset.prod_singleton _ _


@[main]
private lemma limits.concat
  [Fintype β] [CommMonoid γ]
  {m : ℕ}
  {f : (Fin (m + 1) → β) → γ} :
-- imply
  ∏ a : β, ∏ v : Fin m → β, f (Fin.cons a v) = ∏ w : Fin (m + 1) → β, f w := by
-- proof
  rw [← Fintype.prod_prod_type']
  exact Fintype.prod_equiv (Fin.consEquiv (fun _ => β)) _ _ (fun _ => rfl)


@[main]
private lemma limits.domain_defined
  [CommMonoid α]
  {k : ℕ}
  {x : Fin k → ℤ}
  {f : Fin k → ℕ}
  {h : ℤ → ℕ → α} :
-- imply
  ∏ i, ∏ j ∈ Finset.range (f i), h (x i) j = ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < k), ∏ j ∈ Finset.range (f i), h (x i) j := by
-- proof
  rw [Finset.filter_true_of_mem (fun i _ => i.isLt)]


@[main]
private lemma limits.domain_defined.delete
  [CommMonoid α]
  {k : ℕ}
  {x : Fin k → ℤ}
  {f : Fin k → ℕ}
  {h : ℤ → ℕ → α} :
-- imply
  ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < k), ∏ j ∈ Finset.range (f i), h (x i) j = ∏ i, ∏ j ∈ Finset.range (f i), h (x i) j := by
-- proof
  rw [Finset.filter_true_of_mem (fun i _ => i.isLt)]


@[main]
private lemma limits.swap
  [CommMonoid α]
  {m n : ℕ}
  {f : ℕ → ℕ → α} :
-- imply
  ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range n, f i j = ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range m, f i j := by
-- proof
  exact Finset.prod_comm


@[main]
private lemma limits.swap.intlimit
  [CommMonoid α]
  {a d n : ℤ}
  {f : ℤ → ℤ → α} :
-- imply
  ∏ j ∈ Finset.Ico a n, ∏ i ∈ Finset.Ico (a + d) (j + d), f i j = ∏ i ∈ Finset.Ico (a + d) (n + d - 1), ∏ j ∈ Finset.Ico (i - d + 1) n, f i j := by
-- proof
  apply Finset.prod_comm'
  intro j i
  simp only [Finset.mem_Ico]
  omega


@[main]
private lemma limits.swap.subst
  [CommMonoid α]
  {A : Finset ι}
  {s : ι → Finset κ}
  {f : κ → ι → α} :
-- imply
  ∏ j ∈ A, ∏ i ∈ s j, f i j = ∏ i ∈ A, ∏ j ∈ s i, f j i := by
-- proof
  rfl


-- created on 2026-09-27
