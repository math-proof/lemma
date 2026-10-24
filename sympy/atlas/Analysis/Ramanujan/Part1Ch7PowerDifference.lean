/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7PowerDifference.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Ramanujan's Notebooks, Part I, Chapter 7: power-difference series

The parametrized sum `φ_r(x) = ∑_{j ≥ 0} ((j + 1)ʳ - (j + 1 + x)ʳ)` of
B. C. Berndt, *Ramanujan's Notebooks, Part I* (Springer, 1985), Chapter 7,
shared by Entries 9 and 10 of that chapter.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

noncomputable section

/-- `x` is admissible when no shifted base `j + 1 + x` vanishes, i.e. `x ∉ {-1, -2, …}`. -/
def chapter7Admissible (x : ℂ) : Prop :=
  ∀ j : ℕ, (j + 1 : ℂ) + x ≠ 0

/-- The `j`-th term `(j + 1)ʳ - (j + 1 + x)ʳ` of the series defining `φ_r(x)`. -/
def chapter7PowerDifferenceTerm (r x : ℂ) (j : ℕ) : ℂ :=
  Complex.cpow (j + 1 : ℂ) r - Complex.cpow ((j + 1 : ℂ) + x) r

/-- The power-difference series `φ_r(x) = ∑_{j ≥ 0} ((j + 1)ʳ - (j + 1 + x)ʳ)`. -/
def chapter7PowerDifferenceSum (r x : ℂ) : ℂ :=
  ∑' j : ℕ, chapter7PowerDifferenceTerm r x j
end
