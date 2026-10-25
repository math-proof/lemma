/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/PrimeValueConditions.lean -/


import Def.Algebra.Polynomial.PrimeValueConditions
open scoped Polynomial


example (f : ℤ[X]) :
    Polynomial.BunyakovskyCondition f ↔
      1 ≤ f.degree ∧ Irreducible f ∧ 0 < f.leadingCoeff :=
  Iff.rfl

example (fs : Finset ℤ[X]) :
    Polynomial.SchinzelCondition fs ↔
      ∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ f ∈ fs, ¬(p : ℤ) ∣ f.eval (n : ℤ) :=
  Iff.rfl

#print axioms Polynomial.BunyakovskyCondition
#print axioms Polynomial.SchinzelCondition

