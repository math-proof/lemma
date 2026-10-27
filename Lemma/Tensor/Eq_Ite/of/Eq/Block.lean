import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n m : ℕ}
  {a c : Fin n → ℝ}
  {b d : Fin m → ℝ}
  {x : ℝ}
-- given
  (h₀ : Sum.elim a b = Sum.elim c d) :
-- imply
  a = c ∧ b = d ∧ ∀ k, Sum.elim (fun i => a i + x) (fun j => b j + x) k = Sum.elim a b k + x := by
-- proof
  constructor
  ·
    funext i
    have := congr_fun h₀ (Sum.inl i)
    simpa using this
  ·
    constructor
    ·
      funext j
      have := congr_fun h₀ (Sum.inr j)
      simpa using this
    ·
      intro k
      cases k with
      | inl i =>
        simp
      | inr j =>
        simp


-- created on 2023-04-29
-- updated on 2026-10-26
