import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {p : ℕ → Prop}
  {q : ℕ → ℕ → Prop} :
-- imply
  (∀ i < n, ∀ j < n, p j ∧ q i j) ↔
    ∀ j < n, p j ∧ ∀ i < n, q i j := by
-- proof
  constructor
  · intro h j hj
    refine ⟨(h 0 (by omega) j hj).1, fun i hi => (h i hi j hj).2⟩
  · rintro h i hi j hj
    obtain ⟨hp, hq⟩ := h j hj
    exact ⟨hp, hq i hi⟩


-- created on 2023-06-06
