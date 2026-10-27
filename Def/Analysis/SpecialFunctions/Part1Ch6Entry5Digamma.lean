/-
Author: @akiezun, Avocado
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecificLimits.Normed
/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 5

The factorial series `C(x) = ∑_{j ≥ 0} (-1)ʲ / ((x + 1) ⋯ (x + j + 1))` converges for `0 < x` and
has the asymptotic expansion `C(x) ~ ∑_{j ≥ 0} (-1)ʲ B_{j+1} / x^{j+1}` as `x → ∞`, where `B_n` is
the `n`-th Bell number.
-/


namespace Ramanujan.Part1Ch6

namespace Entry5Digamma

open Asymptotics Filter Finset

noncomputable section

/-- The `j`-th term `(-1)ʲ / ((x + 1)(x + 2) ⋯ (x + j + 1))` of Ramanujan's factorial series. -/
def chapter6Section13ExampleCTerm (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j /
    ∏ r ∈ range (j + 1), (x + (r + 1 : ℕ))

/-- The sum `∑_{j ≥ 0} (-1)ʲ / ((x + 1) ⋯ (x + j + 1))` of the factorial series; it converges for
`0 < x` (`summable_chapter6Section13ExampleCTerm`). -/
def chapter6Section13ExampleCSum (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter6Section13ExampleCTerm x j

end
end Entry5Digamma
end Ramanujan.Part1Ch6
