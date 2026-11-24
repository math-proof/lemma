module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Def.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR.Part2
public import Theorem.Finset.Enumerative.ULDMotzkinNumberOfRankR
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Def.Combinatorics.Enumerative.CubicLatticeColoredMotzkin


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CubicLatticeColoredMotzkin.lean -/
namespace MetaMathlibExt

/-- Value of the flat color index. -/
theorem flatIndex_val (n : ℕ) (x : Fin (n + 1) × Bool)
    (h : ¬x.1 = Fin.last n) :
    (flatIndex n x h).val = x.1.val * 2 + (if x.2 then 1 else 0) := rfl

end MetaMathlibExt
