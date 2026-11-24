module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

def embedMarked (n : ℕ) (m : Marked n) : Park (n + 1) :=
  ⟨markedFun n m.1.1 m.2.1, markedFun_mono n m.1.1 m.1.2 m.2.1,
    fun k => markedFun_bound n m.1.1 m.1.2 m.2.1 k⟩

end MetaMathlibExt
end
