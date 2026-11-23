/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PalindromicCompositionsWithoutTwo.lean -/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.PalindromicCompositionsWithoutTwo.Part2

@[expose] public section

namespace MetaMathlibExt

def compSet' (m : ℕ) : Set (List ℕ) :=
    {d | (∀ p ∈ d, 0 < p) ∧ (∀ p ∈ d.tail, p ≠ 2) ∧ d.sum = m}

def head2Set (k : ℕ) : Set (List ℕ) := {d | d ∈ compSet' (k + 1) ∧ d.headI = 2}

end MetaMathlibExt
