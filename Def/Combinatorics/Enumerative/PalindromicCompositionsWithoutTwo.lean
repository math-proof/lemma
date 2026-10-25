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
def psi : List ℕ → List ℕ
  | [] => []
  | [a] => if a = 1 then [] else [2 * (a - 1)]
  | a :: x :: rest => x :: psi (a :: rest) ++ [x]
termination_by l => l.length

/-- Inverse of `psi`: unfold a palindrome into a composition. -/
def phi (c : List ℕ) : List ℕ :=
  c.bidirectionalRecOn [1] (fun m => [m / 2 + 1]) (fun a _l _b ih => ih.headI :: a :: ih.tail)

end MetaMathlibExt
