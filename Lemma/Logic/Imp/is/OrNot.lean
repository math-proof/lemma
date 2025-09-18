import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main :
-- imply
  p → q ↔ ¬p ∨ q := by
-- proof
  constructor <;>
    intro h
  .
    by_cases hp : p
    exact Or.inr (h hp)
    exact Or.inl hp
  .
    intro hp
    match h with
    | Or.inl hnp =>
      contradiction
    | Or.inr hq =>
      exact hq


-- created on 2024-07-01
