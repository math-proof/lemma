/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


section

open scoped BigOperators

namespace MetaMathlibExt

abbrev binomialTMotzkinStep (t : ℕ) := Σ k : Fin (t + 1), Fin (Nat.choose t k)

abbrev binomialTMotzkinHeight (t : ℕ) : binomialTMotzkinStep t → ℤ :=
  fun s => 1 - (s.1 : ℤ)

end MetaMathlibExt
end
