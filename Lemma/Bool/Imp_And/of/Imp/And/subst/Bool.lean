import sympy.Basic


@[main]
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
  rw [if_pos hpc.2]
  exact h hpc


-- created on 2023-04-25
