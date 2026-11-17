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
public import Def.Combinatorics.Enumerative.PalindromicCompositionsWithoutTwo

public section

namespace MetaMathlibExt

@[simp] theorem phi_nil : phi [] = [1] := by simp [phi]

@[simp] theorem phi_singleton (m : ℕ) : phi [m] = [m / 2 + 1] := by simp [phi]

@[simp] theorem phi_cons_append (a b : ℕ) (l : List ℕ) :
    phi (a :: (l ++ [b])) = (phi l).headI :: a :: (phi l).tail := by
  simp only [phi, List.bidirectionalRecOn]; rw [List.bidirectionalRec_cons_append]

end MetaMathlibExt
