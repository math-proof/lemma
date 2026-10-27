import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n m : ℕ}
  {a : Fin n → ℝ}
  {b : Fin m → ℝ} :
-- imply
  ∀ k : Fin n ⊕ Fin m, -(Sum.elim a b k) = Sum.elim (fun i => -a i) (fun j => -b j) k := by
-- proof
  intro k
  cases k with
  | inl i =>
    simp
  | inr j =>
    simp


-- created on 2023-09-18
-- updated on 2026-10-26
