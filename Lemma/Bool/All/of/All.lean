import sympy.Basic


@[main]
private lemma limits.swap
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop}
-- given
  (h : ∀ x ∈ A, ∀ y ∈ B, f x y) :
-- imply
  ∀ y ∈ B, ∀ x ∈ A, f x y :=
-- proof
  fun y hy x hx => h x hx y hy


@[main]
private lemma subst
  {A : Set ι}
  {n : ι → ℕ}
  {p : ι → ℕ → Prop}
-- given
  (h : ∀ i ∈ A, ∀ x < n i + 1, p i x) :
-- imply
  ∀ i ∈ A, p i (n i) :=
-- proof
  fun i hi => h i hi (n i) (Nat.lt_succ_self _)


@[main]
private lemma limits.delete
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop}
-- given
  (h : ∀ y, ∀ x ∈ A, f x y) :
-- imply
  ∀ y ∈ B, ∀ x ∈ A, f x y :=
-- proof
  fun y _ => h y


@[main]
private lemma limits.insert
  {A : Set α}
  {B : Set β}
  {f : α → β → Prop}
-- given
  (h : ∀ y, ∀ x ∈ A, f x y) :
-- imply
  ∀ y ∈ B, ∀ x ∈ A, f x y :=
-- proof
  fun y _ => h y


@[main]
private lemma limits.invert
  {f g : α → Prop}
-- given
  (h : ∀ e, g e → f e) :
-- imply
  ∀ e, ¬f e → ¬g e :=
-- proof
  fun e hf hg => hf (h e hg)


@[main]
private lemma limits.domain_defined.given
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h₀ : m ≤ n)
  (h₁ : ∀ i ∈ Finset.range (min m n), p i) :
-- imply
  ∀ i ∈ Finset.range m, p i := by
-- proof
  rwa [min_eq_left h₀] at h₁


@[main]
private lemma limits.domain_defined
  {m n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : ∀ i ∈ Finset.range m, p i) :
-- imply
  ∀ i ∈ Finset.range (min m n), p i := by
-- proof
  intro i hi
  simp only [Finset.mem_range, lt_min_iff] at hi
  exact h i (Finset.mem_range.mpr hi.1)


-- created on 2026-09-27
