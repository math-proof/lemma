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
import Abbrev.Combinatorics.Enumerative.BinomialTMotzkinPaths


section

open scoped BigOperators

namespace MetaMathlibExt

noncomputable def binomialTMotzkinCount (t n : ℕ) (h : ℤ) : ℕ :=
  Fintype.card {p : Fin n → binomialTMotzkinStep t //
    (∀ m : Fin (n + 1),
      0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0) ∧
    ∑ i : Fin n, binomialTMotzkinHeight t (p i) = h}

end MetaMathlibExt
end
