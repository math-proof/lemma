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
public import Abbrev.Combinatorics.Enumerative.BinomialTMotzkinPaths

@[expose] public section

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
