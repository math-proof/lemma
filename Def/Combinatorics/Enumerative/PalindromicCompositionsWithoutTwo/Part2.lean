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
import Theorem.Combinatorics.Enumerative.PalindromicCompositionsWithoutTwo


namespace MetaMathlibExt

def compSet (m : ℕ) : Set (List ℕ) := {c | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = m}

def palSet (n : ℕ) : Set (List ℕ) :=
    {c | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = n ∧ c.reverse = c}

/-- Odd-parity analogue of `psi`: the head `a` becomes the odd middle `2a-1`. -/
def psiO : List ℕ → List ℕ
  | [] => []
  | [a] => [2 * a - 1]
  | a :: x :: rest => x :: psiO (a :: rest) ++ [x]
termination_by l => l.length

def phiO (c : List ℕ) : List ℕ :=
  c.bidirectionalRecOn [] (fun m => [(m + 1) / 2]) (fun a _l _b ih => ih.headI :: a :: ih.tail)

end MetaMathlibExt
