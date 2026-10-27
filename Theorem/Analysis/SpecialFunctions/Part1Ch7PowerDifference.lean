/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Def.Analysis.SpecialFunctions.Part1Ch7PowerDifference
/-!
# Ramanujan's Notebooks, Part I, Chapter 7: power-difference series

The parametrized sum `φ_r(x) = ∑_{j ≥ 0} ((j + 1)ʳ - (j + 1 + x)ʳ)` of
B. C. Berndt, *Ramanujan's Notebooks, Part I* (Springer, 1985), Chapter 7,
shared by Entries 9 and 10 of that chapter.
-/


namespace Ramanujan.Part1Ch7

noncomputable section

@[simp]
theorem chapter7Admissible_zero : chapter7Admissible 0 := by
  intro j
  rw [add_zero]
  exact_mod_cast Nat.succ_ne_zero j

@[simp]
theorem chapter7PowerDifferenceTerm_zero_left (x : ℂ) (j : ℕ) :
    chapter7PowerDifferenceTerm 0 x j = 0 := by
  simp [chapter7PowerDifferenceTerm]

@[simp]
theorem chapter7PowerDifferenceTerm_zero_right (r : ℂ) (j : ℕ) :
    chapter7PowerDifferenceTerm r 0 j = 0 := by
  simp [chapter7PowerDifferenceTerm]

end
end Ramanujan.Part1Ch7
