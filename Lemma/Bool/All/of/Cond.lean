import sympy.Basic


@[path]
private lemma main
  {r : Prop}
-- given
  (h : r) :
-- imply
  ∀ _ : α, r :=
-- proof
  fun _ => h


@[path]
private lemma subst.given
  {n : ℕ}
  {p : ℕ → Prop}
-- given
  (h : ∀ m < n + 1, p m) :
-- imply
  ∀ x < n + 1, p x :=
-- proof
  h


@[path]
private lemma subst
  {e : α}
  {p : α → Prop}
-- given
  (h : p e) :
-- imply
  ∀ e' ∈ ({e} : Set α), p e' := by
-- proof
  intro e' he'
  rw [Set.mem_singleton_iff.mp he']
  exact h


@[path]
private lemma domain_defined
  {D : Set α}
  {p : α → Prop}
-- given
  (h : ∀ x, x ∈ D → p x) :
-- imply
  ∀ x ∈ D, p x :=
-- proof
  h


-- created on 2018-12-13
-- updated on 2026-08-28
-- updated on 2026-09-27
