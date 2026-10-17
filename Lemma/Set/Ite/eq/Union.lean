import sympy.Basic


@[path]
private lemma main
  {p q : Prop} [Decidable p] [Decidable q]
  {s : Set α} :
-- imply
  (if p ∧ q then s else Set.univ) = (if p then s else Set.univ) ∪ (if q then s else Set.univ) := by
-- proof
  ext x
  by_cases hp : p
  <;> by_cases hq : q
  <;> simp [hp, hq]


-- created on 2026-10-11
-- updated on 2026-10-17
