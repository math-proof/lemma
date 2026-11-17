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
public import Def.Combinatorics.Enumerative.PalindromicCompositionsWithoutTwo.Part2

public section

namespace MetaMathlibExt

@[simp] theorem phiO_singleton (m : ℕ) : phiO [m] = [(m + 1) / 2] := by simp [phiO]

@[simp] theorem phiO_cons_append (a b : ℕ) (l : List ℕ) :
    phiO (a :: (l ++ [b])) = (phiO l).headI :: a :: (phiO l).tail := by
  simp only [phiO, List.bidirectionalRecOn]; rw [List.bidirectionalRec_cons_append]

end MetaMathlibExt
