/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Composite.lean -/


import sympy.atlas.NumberTheory.Composite
import Lemma.Nat.Composite

example : Nat.IsComposite 4 := by
  change 1 < 4 ∧ ¬ Nat.Prime 4
  exact ⟨by decide, by decide⟩

example : ¬ Nat.IsComposite 0 := by
  intro h
  have hlt := h.one_lt
  omega

example : ¬ Nat.IsComposite 1 := by
  intro h
  have hlt := h.one_lt
  omega

example : ¬ Nat.IsComposite 2 := by
  intro h
  have hnp := h.not_prime
  exact hnp (by decide)

example : ¬ Nat.IsComposite 7 := by
  intro h
  have hnp := h.not_prime
  exact hnp (by decide)

example (h : Nat.IsComposite 4) : 1 < 4 :=
  h.one_lt

example (h : Nat.IsComposite 4) : ¬ Nat.Prime 4 :=
  h.not_prime
