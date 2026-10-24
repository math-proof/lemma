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

namespace MetaMathlibExt

/-- Fold a composition `a :: h'` of `k+1` into a palindrome of `2k`: the tail `h'`
becomes the outer half and `a` determines the (possibly empty) even middle part. -/
private def psi : List ℕ → List ℕ
  | [] => []
  | [a] => if a = 1 then [] else [2 * (a - 1)]
  | a :: x :: rest => x :: psi (a :: rest) ++ [x]
termination_by l => l.length

/-- Inverse of `psi`: unfold a palindrome into a composition. -/
private def phi (c : List ℕ) : List ℕ :=
  c.bidirectionalRecOn [1] (fun m => [m / 2 + 1]) (fun a _l _b ih => ih.headI :: a :: ih.tail)

@[simp] private theorem phi_nil : phi [] = [1] := by simp [phi]
@[simp] private theorem phi_singleton (m : ℕ) : phi [m] = [m / 2 + 1] := by simp [phi]
@[simp] private theorem phi_cons_append (a b : ℕ) (l : List ℕ) :
    phi (a :: (l ++ [b])) = (phi l).headI :: a :: (phi l).tail := by
  simp only [phi, List.bidirectionalRecOn]; rw [List.bidirectionalRec_cons_append]

private def compSet (m : ℕ) : Set (List ℕ) := {c | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = m}
private def palSet (n : ℕ) : Set (List ℕ) :=
    {c | (∀ a ∈ c, 0 < a ∧ a ≠ 2) ∧ c.sum = n ∧ c.reverse = c}

/-- Odd-parity analogue of `psi`: the head `a` becomes the odd middle `2a-1`. -/
private def psiO : List ℕ → List ℕ
  | [] => []
  | [a] => [2 * a - 1]
  | a :: x :: rest => x :: psiO (a :: rest) ++ [x]
termination_by l => l.length

private def phiO (c : List ℕ) : List ℕ :=
  c.bidirectionalRecOn [] (fun m => [(m + 1) / 2]) (fun a _l _b ih => ih.headI :: a :: ih.tail)

@[simp] private theorem phiO_singleton (m : ℕ) : phiO [m] = [(m + 1) / 2] := by simp [phiO]
@[simp] private theorem phiO_cons_append (a b : ℕ) (l : List ℕ) :
    phiO (a :: (l ++ [b])) = (phiO l).headI :: a :: (phiO l).tail := by
  simp only [phiO, List.bidirectionalRecOn]; rw [List.bidirectionalRec_cons_append]

private def compSet' (m : ℕ) : Set (List ℕ) :=
    {d | (∀ p ∈ d, 0 < p) ∧ (∀ p ∈ d.tail, p ≠ 2) ∧ d.sum = m}

private def head2Set (k : ℕ) : Set (List ℕ) := {d | d ∈ compSet' (k + 1) ∧ d.headI = 2}
end MetaMathlibExt
