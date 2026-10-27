import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {lhs : α}
  {rhs : Set α}
-- given
  (h₀ : lhs ∈ rhs) :
-- imply
  ∃ v ∈ rhs, lhs = v :=
-- proof
  ⟨lhs, h₀, rfl⟩


-- created on 2021-07-26
-- updated on 2026-10-26
