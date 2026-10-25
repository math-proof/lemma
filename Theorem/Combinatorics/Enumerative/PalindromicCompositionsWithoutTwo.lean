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
import Def.Combinatorics.Enumerative.PalindromicCompositionsWithoutTwo


namespace MetaMathlibExt

@[simp] theorem phi_nil : phi [] = [1] := by simp [phi]

@[simp] theorem phi_singleton (m : ℕ) : phi [m] = [m / 2 + 1] := by simp [phi]

@[simp] theorem phi_cons_append (a b : ℕ) (l : List ℕ) :
    phi (a :: (l ++ [b])) = (phi l).headI :: a :: (phi l).tail := by
  simp only [phi, List.bidirectionalRecOn]; rw [List.bidirectionalRec_cons_append]

end MetaMathlibExt
