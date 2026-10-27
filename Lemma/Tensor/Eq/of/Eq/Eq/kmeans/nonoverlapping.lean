import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {k : ℕ}
  {d : Fin k → ℝ}
  {i j : Fin k}
-- given
  (h₀ : d i < d j) :
-- imply
  i ≠ j ∧ (if d i ≤ d j then i else j) = i := by
-- proof
  constructor
  ·
    intro hij
    simp [hij] at h₀
  ·
    have hle : d i ≤ d j := le_of_lt h₀
    simp [hle]


-- created on 2020-12-24
-- updated on 2026-10-26
