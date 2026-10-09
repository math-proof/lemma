import sympy.Basic


@[path]
private lemma doit.inner
  {a m : ℕ}
  {p : ℕ → ℕ → Prop} :
-- imply
  (∀ i < m, ∀ j ∈ Finset.Ico a (a + 2), p i j) ↔ ∀ i < m, p i a ∧ p i (a + 1) := by
-- proof
  constructor
  ·
    intro h i hi
    exact ⟨h i hi a (by simp), h i hi (a + 1) (by simp)⟩
  ·
    intro h i hi j hj
    simp only [Finset.mem_Ico] at hj
    rcases (show j = a ∨ j = a + 1 by omega) with rfl | rfl
    ·
      exact (h i hi).1
    ·
      exact (h i hi).2


@[path]
private lemma limits.swap
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop} :
-- imply
  (∀ y ∈ B, ∀ x ∈ A, f x y) ↔ ∀ x ∈ A, ∀ y ∈ B, f x y :=
-- proof
  ⟨fun h x hx y hy => h y hy x hx, fun h y hy x hx => h x hx y hy⟩


@[path]
private lemma limits.domain_defined
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : m ≤ n) :
-- imply
  (∀ i ∈ Finset.range m, p i) ↔ ∀ i ∈ Finset.range (min m n), p i := by
-- proof
  rw [min_eq_left h]


@[path]
private lemma limits.swap.intlimit
  {a d n : ℤ}
  {f : ℤ → ℤ → Prop} :
-- imply
  (∀ j, a + 1 ≤ j → j < n → ∀ i, a + d ≤ i → i < j + d → f i j) ↔ ∀ i, a + d ≤ i → i < n - 1 + d → ∀ j, i - d + 1 ≤ j → j < n → f i j := by
-- proof
  constructor
  ·
    intro h i hi₀ hi₁ j hj₀ hj₁
    exact h j (by omega) hj₁ i hi₀ (by omega)
  ·
    intro h j hj₀ hj₁ i hi₀ hi₁
    exact h i hi₀ (by omega) j (by omega) hj₁


@[path]
private lemma limits.swap.subst
  {A : Set ι}
  {s : ι → Set κ}
  {f : κ → ι → Prop} :
-- imply
  (∀ j ∈ A, ∀ i ∈ s j, f i j) ↔ ∀ i ∈ A, ∀ j ∈ s i, f j i :=
-- proof
  Iff.rfl


@[path]
private lemma doit.outer.setlimit
  {a : ι}
  {q p : ι → κ → Prop} :
-- imply
  (∀ i ∈ ({a} : Set ι), ∀ j, q i j → p i j) ↔ ∀ j, q a j → p a j := by
-- proof
  simp


@[path]
private lemma limits.separate
  {n : ℕ}
  {f : ℕ → Prop}
  {g : ℕ → ℕ → Prop}
-- given
  (h : 0 < n) :
-- imply
  (∀ j < n, ∀ i < n, f j ∧ g i j) ↔ ∀ j < n, f j ∧ ∀ i < n, g i j := by
-- proof
  constructor
  ·
    intro h' j hj
    exact ⟨(h' j hj 0 h).1, fun i hi => (h' j hj i hi).2⟩
  ·
    intro h' j hj i hi
    exact ⟨(h' j hj).1, (h' j hj).2 i hi⟩


-- created on 2026-09-27
