/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 6

Harmonic partial sum equals r plus a weighted 27k³-3k reciprocal sum.
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry6

/-- `A n k = 3 ^ k * n + (3 ^ k - 1) / 2`, the sequence with `A n 0 = n` and
`A n (k + 1) = 3 * A n k + 1`. -/
def A (n k : ℕ) : ℕ := 3 ^ k * n + (3 ^ k - 1) / 2

end Entry6
end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
