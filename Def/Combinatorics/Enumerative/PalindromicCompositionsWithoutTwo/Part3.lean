/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PalindromicCompositionsWithoutTwo.lean -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.PalindromicCompositionsWithoutTwo.Part2


namespace MetaMathlibExt

def compSet' (m : ℕ) : Set (List ℕ) :=
    {d | (∀ p ∈ d, 0 < p) ∧ (∀ p ∈ d.tail, p ≠ 2) ∧ d.sum = m}

def head2Set (k : ℕ) : Set (List ℕ) := {d | d ∈ compSet' (k + 1) ∧ d.headI = 2}

end MetaMathlibExt
