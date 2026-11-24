import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
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


-- created on 2022-01-28
-- updated on 2026-11-24
