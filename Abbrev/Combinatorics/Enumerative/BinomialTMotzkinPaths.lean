/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean -/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section


section

open scoped BigOperators

namespace MetaMathlibExt

abbrev binomialTMotzkinStep (t : ℕ) := Σ k : Fin (t + 1), Fin (Nat.choose t k)

abbrev binomialTMotzkinHeight (t : ℕ) : binomialTMotzkinStep t → ℤ :=
  fun s => 1 - (s.1 : ℤ)

end MetaMathlibExt
end
