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
public import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

def markedFun (n : ℕ) (a : Fin n → Fin n) (i0 : Fin n) :
    Fin (n + 1) → Fin (n + 1) :=
  fun k =>
    if h0 : k.val = 0 then ⟨0, by omega⟩
    else if h1 : k.val - 1 < i0.val then
      ⟨(a ⟨k.val - 1, by omega⟩).val, by
        have _h1 := (a ⟨k.val - 1, by omega⟩).isLt
        omega⟩
    else
      ⟨(a ⟨k.val - 1, by omega⟩).val + 1, by
        have _h1 := (a ⟨k.val - 1, by omega⟩).isLt
        omega⟩

end MetaMathlibExt
end
