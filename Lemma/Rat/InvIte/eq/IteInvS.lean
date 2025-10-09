import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  [Inv α]
-- given
  (a b : α) :
-- imply
  (if p then
    a⁻¹
  else
    b⁻¹) = (if p then
    a
  else
    b)⁻¹ := by
-- proof
  split_ifs with h <;> rfl


-- created on 2025-10-09
