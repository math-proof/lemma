import Initialize.Tactic.Attr.Basic


@[path]
private lemma given
  {p c : Prop} [Decidable c]
  {x z : α}
  {P : α → Prop}
-- given
  (h : p ∧ c → P x) :
-- imply
  p ∧ c → P (if c then x else z) := by
-- proof
  intro hpc
  rw [ite_eq_left hpc.2]
  exact h hpc


-- created on 2023-04-25
-- updated on 2026-10-26
