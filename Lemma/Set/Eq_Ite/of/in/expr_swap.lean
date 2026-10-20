import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {f g : β} :
-- imply
  (if p then f else g) = if ¬p then g else f := by
-- proof
  if hp : p then
    simp [hp]
  else
    simp [hp]


-- created on 2020-10-27
-- updated on 2026-10-17
