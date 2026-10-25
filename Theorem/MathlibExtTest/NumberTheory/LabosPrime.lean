/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LabosPrime.lean -/


import Def.NumberTheory.LabosPrime
import Mathlib.Tactic


namespace MetaMathlibExt

example (n L : ℕ) (h : IsLabosPrime n L) : 1 ≤ n := h.1

example (n L : ℕ) (h : IsLabosPrime n L) : 0 < L := h.2.1

example (n L : ℕ) (h : IsLabosPrime n L) :
    Nat.primeCounting L - Nat.primeCounting (L / 2) = n :=
  h.2.2.1

example (n L m : ℕ) (h : IsLabosPrime n L) (hm : 0 < m) (hml : m < L) :
    Nat.primeCounting m - Nat.primeCounting (m / 2) ≠ n :=
  h.2.2.2 m hm hml

example (L : ℕ) : ¬ IsLabosPrime 0 L := by
  simp [IsLabosPrime]

example : IsLabosPrime 1 2 := by
  refine ⟨by omega, by omega, ?_, ?_⟩
  · decide
  · intro m hm hml
    have hm_eq : m = 1 := by omega
    subst m
    decide

#print axioms IsLabosPrime

end MetaMathlibExt
