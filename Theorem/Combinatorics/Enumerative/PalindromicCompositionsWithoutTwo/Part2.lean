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
import Def.Combinatorics.Enumerative.PalindromicCompositionsWithoutTwo.Part2


namespace MetaMathlibExt

@[simp] theorem phiO_singleton (m : ℕ) : phiO [m] = [(m + 1) / 2] := by simp [phiO]

@[simp] theorem phiO_cons_append (a b : ℕ) (l : List ℕ) :
    phiO (a :: (l ++ [b])) = (phiO l).headI :: a :: (phiO l).tail := by
  simp only [phiO, List.bidirectionalRecOn]; rw [List.bidirectionalRec_cons_append]

end MetaMathlibExt
