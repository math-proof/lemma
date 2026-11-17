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
public import Theorem.Combinatorics.Enumerative.PalindromicCompositionsWithoutTwo

@[expose] public section

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
