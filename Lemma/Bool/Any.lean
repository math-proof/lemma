import sympy.Basic


@[path]
private lemma limits.swap.intlimit
  {a d n : ℤ}
  {f : ℤ → ℤ → Prop} :
-- imply
  (∃ j, a + 1 ≤ j ∧ j < n ∧ ∃ i, a + d ≤ i ∧ i < j + d ∧ f i j) ↔ ∃ i, a + d ≤ i ∧ i < n - 1 + d ∧ ∃ j, i - d + 1 ≤ j ∧ j < n ∧ f i j := by
-- proof
  constructor
  ·
    rintro ⟨j, hj₀, hj₁, i, hi₀, hi₁, h⟩
    exact ⟨i, hi₀, by omega, j, by omega, hj₁, h⟩
  ·
    rintro ⟨i, hi₀, hi₁, j, hj₀, hj₁, h⟩
    exact ⟨j, by omega, hj₁, i, hi₀, by omega, h⟩


@[path]
private lemma limits.swap.subst
  {A : Set ι}
  {s : ι → Set κ}
  {f : κ → ι → Prop} :
-- imply
  (∃ j ∈ A, ∃ i ∈ s j, f i j) ↔ ∃ i ∈ A, ∃ j ∈ s i, f j i :=
-- proof
  Iff.rfl


@[path]
private lemma doit.inner.setlimit
  {a b : ι}
  {m : ℕ}
  {x : ℕ → ι → Prop} :
-- imply
  (∃ i < m, ∃ j ∈ ({a, b} : Set ι), x i j) ↔ ∃ i < m, x i a ∨ x i b := by
-- proof
  simp


@[path]
private lemma doit.inner
  {a m : ℕ}
  {p : ℕ → ℕ → Prop} :
-- imply
  (∃ i < m, ∃ j ∈ Finset.Ico a (a + 2), p i j) ↔ ∃ i < m, p i a ∨ p i (a + 1) := by
-- proof
  constructor
  ·
    rintro ⟨i, hi, j, hj, h⟩
    simp only [Finset.mem_Ico] at hj
    rcases (show j = a ∨ j = a + 1 by omega) with rfl | rfl
    ·
      exact ⟨i, hi, Or.inl h⟩
    ·
      exact ⟨i, hi, Or.inr h⟩
  ·
    rintro ⟨i, hi, h | h⟩
    ·
      exact ⟨i, hi, a, by simp, h⟩
    ·
      exact ⟨i, hi, a + 1, by simp, h⟩


@[path]
private lemma limits.domain_defined
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : m ≤ n) :
-- imply
  (∃ i ∈ Finset.range m, p i) ↔ ∃ i ∈ Finset.range (min m n), p i := by
-- proof
  rw [min_eq_left h]


@[path]
private lemma limits.separate
  {n : ℕ}
  {f : ℕ → Prop}
  {g : ℕ → ℕ → Prop} :
-- imply
  (∃ j < n, ∃ i < n, f j ∧ g i j) ↔ ∃ j < n, f j ∧ ∃ i < n, g i j := by
-- proof
  constructor
  ·
    rintro ⟨j, hj, i, hi, hf, hg⟩
    exact ⟨j, hj, hf, i, hi, hg⟩
  ·
    rintro ⟨j, hj, hf, i, hi, hg⟩
    exact ⟨j, hj, i, hi, hf, hg⟩


@[path]
private lemma limits.swap
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop} :
-- imply
  (∃ y ∈ B, ∃ x ∈ A, f x y) ↔ ∃ x ∈ A, ∃ y ∈ B, f x y :=
-- proof
  ⟨fun ⟨y, hy, x, hx, h⟩ => ⟨x, hx, y, hy, h⟩, fun ⟨x, hx, y, hy, h⟩ => ⟨y, hy, x, hx, h⟩⟩


-- created on 2026-09-27
