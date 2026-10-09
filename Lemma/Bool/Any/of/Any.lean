import sympy.sets.sets
import sympy.Basic


@[path]
private lemma limits.swap.given
  {A : Set α}
  {f : β → Prop}
  {g : α → β → Prop}
-- given
  (h : ∃ x ∈ A, ∃ y, f y ∧ g x y) :
-- imply
  ∃ y, f y ∧ ∃ x ∈ A, g x y := by
-- proof
  obtain ⟨x, hx, y, hy, hg⟩ := h
  exact ⟨y, hy, x, hx, hg⟩


@[path]
private lemma limits.swap
  {A : Set α}
  {f : β → Prop}
  {g : α → β → Prop}
-- given
  (h : ∃ y, f y ∧ ∃ x ∈ A, g x y) :
-- imply
  ∃ x ∈ A, ∃ y, f y ∧ g x y := by
-- proof
  obtain ⟨y, hy, x, hx, hg⟩ := h
  exact ⟨x, hx, y, hy, hg⟩


@[path]
private lemma limits.relax
  [Preorder α]
  {a b : α}
  {p : α → Prop}
-- given
  (h : ∃ x ∈ Ico a b, p x) :
-- imply
  ∃ x ∈ Icc a b, p x := by
-- proof
  obtain ⟨x, hx, hp⟩ := h
  exact ⟨x, Set.Ico_subset_Icc_self hx, hp⟩


@[path]
private lemma limits.relax.subst
  [Preorder α]
  {a b : α}
  {p : α → Prop}
-- given
  (h : ∃ x ∈ Ico a b, p x) :
-- imply
  ∃ y ∈ Icc a b, p y := by
-- proof
  obtain ⟨x, hx, hp⟩ := h
  exact ⟨x, Set.Ico_subset_Icc_self hx, hp⟩


@[path]
private lemma limits.domain_defined.given
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : ∃ i ∈ Finset.range (min m n), p i) :
-- imply
  ∃ i ∈ Finset.range m, p i := by
-- proof
  obtain ⟨i, hi, hp⟩ := h
  simp only [Finset.mem_range, lt_min_iff] at hi
  exact ⟨i, Finset.mem_range.mpr hi.1, hp⟩


@[path]
private lemma limits.domain_defined
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h₀ : ∃ i ∈ Finset.range m, p i)
  (h₁ : m ≤ n) :
-- imply
  ∃ i ∈ Finset.range (min m n), p i := by
-- proof
  rwa [min_eq_left h₁]


-- created on 2026-09-27
