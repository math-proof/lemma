import Lemma.Set.In_Finset
open Set


@[main]
private lemma main
  {a b : α} :
-- imply
  {a} ∪ {b} = ({a, b} : Set α) := by
-- proof
  apply ext
  intro x
  constructor
  ·
    intro h
    obtain h | h := h
    ·
      rw [h]
      apply In_Finset
    ·
      simp [h]
  ·
    intro h
    obtain h | h := h
    ·
      rw [h]
      apply In_Finset
    ·
      rw [h]
      simp


-- created on 2025-04-04
