import sympy.Basic


@[main]
private lemma main
  {p q : Prop}
  [Decidable p] [Decidable q]
  {A B : α} :
-- imply
  (if p ∧ q then A else B) = (if q then (if p then A else B) else B) := by
-- proof
  if hp : p then
    if hq : q then
      simp [hp, hq]
    else
      simp [hp, hq]
  else
    if hq : q then
      simp [hp, hq]
    else
      simp [hp, hq]


-- created on 2020-02-22
-- updated on 2023-06-01
