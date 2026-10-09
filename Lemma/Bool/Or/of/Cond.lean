import sympy.Basic


@[path]
private lemma main
  {p q : Prop}
-- given
  (h : p) :
-- imply
  p ∨ q :=
-- proof
  Or.inl h


@[path]
private lemma split
  {p c : Prop}
-- given
  (h : p) :
-- imply
  p ∧ ¬c ∨ c := by
-- proof
  by_cases hc : c
  ·
    exact Or.inr hc
  ·
    exact Or.inl ⟨h, hc⟩


@[path]
private lemma subst
  {D : Set α}
  {s : α}
  {p : α → Prop}
-- given
  (h : ∀ t ∈ D, p t) :
-- imply
  s ∉ D ∨ p s := by
-- proof
  by_cases hs : s ∈ D
  ·
    exact Or.inr (h s hs)
  ·
    exact Or.inl hs


-- created on 2018-01-03
-- updated on 2026-09-27
