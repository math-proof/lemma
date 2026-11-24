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
public import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

def joinFun (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) : Fin n → Fin n :=
  fun j =>
    if h : j.val < i0.val then
      ⟨(l.1 ⟨j.val, h⟩).val, by
        have h1 := (l.1 ⟨j.val, h⟩).isLt
        have h2 := i0.isLt
        omega⟩
    else
      ⟨(u.1 ⟨j.val - i0.val, by
        have hj := j.isLt
        have hi := i0.isLt
        omega⟩).val + i0.val, by
        have h1 := (u.1 ⟨j.val - i0.val, by
          have hj := j.isLt
          have hi := i0.isLt
          omega⟩).isLt
        have hi := i0.isLt
        omega⟩

end MetaMathlibExt
end
